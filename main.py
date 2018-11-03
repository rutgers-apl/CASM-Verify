import dslparse
import z3
import argparse
import dslinstructions
import x86todsl
from mainhelper import *
from SampleGenerator import *
import depgraph
from functools import reduce
import resource
import sys
import config
import ansiCode
import time
import itertools

sys.setrecursionlimit(10000)

# Command line arguments parsing
parser = argparse.ArgumentParser()
parser.add_argument('--pre', help='file path that stores the pre condition mapping between asm and dsl')
parser.add_argument("--post", help='file path that stores the post condition mapping between asm and dsl')
parser.add_argument('--p1', help='file path for p1')
parser.add_argument('--p2', help='file path for p2')
parser.add_argument('--p1lang', help='is p1 dsl or asm?')
parser.add_argument('--p2lang', help='is p2 dsl or asm?')
parser.add_argument("--verbose", help="increase output verbosity", action="store_true")
parser.add_argument("--arch", help='Architecture of the implementation. Defaults to x86_64. Options: x86_64, x86')
parser.add_argument("--mem_model", type=int, help="Memory model can be based on 8-bit value, or a 32-bit value (assuming there will be 4-byte aligned memory operations. Options: 8, 32) Defaults to 32")
parser.add_argument("--verif_mode", help="Verification Mode.\n" + \
                                        "default: Includes all descendant nodes of two comparing nodes in SMT query. The default value\n" + \
                                        "intersection: Includes intersection of descendant nodes of two comparing nodes in SMT query.\n" + \
                                        "hybrid: Tries intersection first. If SAT, then tries default mode.")
parser.add_argument("--no_alias_analysis", help="Do not perform alias analysis", action="store_true")
parser.add_argument("--timeout", help="How long should query run before calling it time-out (in seconds?)")
parser.add_argument("--z3_check_command", help="A specific check-sat-using command for smt query. defaults to (check-sat-using default)")
parser.add_argument("--max_unknown_count", type=int, help="Number of Unknown results to encounter before exiting verification. Defaults to 1")
args = parser.parse_args()


####################################################################################################
# Configuration based on the command argument
####################################################################################################
ansiCode.Print("%sConfiguring%s" % (ansiCode.bold, ansiCode.reset))
config.SetUpConfig(config, args)


####################################################################################################
#       Create dslinstruction from strings.
#
#    input :
#        preString : precondition String
#        p1String : p1 String
#        p2String : p2 String
#        postString : postcondition String
#    
#    output : 
#        preAst : AST of precondition
#        p1Ast : AST of p1
#        p2Ast : AST of p2
#        postAst : AST of the postcondition
#
####################################################################################################
# Read from file
ansiCode.PrintOnThisLineBold("Reading Files")
preString = readFile(args.pre)
p1String = readFile(args.p1)
p2String = readFile(args.p2)
postString = readFile(args.post)

# Turn everything into dslinstruction
ansiCode.PrintOnThisLineBold("ParsingFiles: ")
ansiCode.Print("pre condition")
preAst = dslparse.dslToAst(preString)



ansiCode.PrintFromLeft("p1", 13)
p1Ast = ParseProgramToDsl(p1String, config.p1lang, "P1")
ansiCode.PrintFromLeft("p2", 2)
p2Ast = ParseProgramToDsl(p2String, config.p2lang, "P2")
ansiCode.PrintFromLeft("post condition", 2)
postAst = dslparse.dslToAst(postString)

# Constant propagate some numbers
ansiCode.PrintFromLeft("Constant propagating", 14)
ConstantPropagate(preAst)
ConstantPropagate(p1Ast)
ConstantPropagate(p2Ast)
ConstantPropagate(postAst)

# Convert variables into SSA Form
ansiCode.PrintFromLeft("Converting to SSA form", 20)
ConvertToSSAForms(preAst, p1Ast, p2Ast, postAst)

# Extract out @DataRegion
preAst, dataRegionAst = ExtractDataRegions(preAst)

####################################################################################################
#    Create dependency graph from AST.
#
#    input :
#        preAst : AST of precondition
#        p1Ast : AST of p1
#        p2Ast : AST of p2
#        postAst : AST of the postcondition
#    
#    output : 
#        preGraph : contains the precondition of the two programs
#        programGraph : contains the graph of p1 and p2 we want to verify equivalent
#        postGraph : contains the postcondition of the two programs
#
####################################################################################################
ansiCode.PrintOnThisLineBold("Constructing DAGs: ")
dataRegionGraph, preGraph, programGraph, postGraph = GetGraphsFromAsts(dataRegionAst, preAst, p1Ast, p2Ast, postAst)
ansiCode.PrintOnThisLine("Preprocessing finished\n")

####################################################################################################
#       Generate random sample inputs
####################################################################################################
ansiCode.PrintOnThisLineBold("Sample inputs : ")
sampGen = SampleGenerator(preGraph, dataRegionGraph)
sampGen.CreateRandomSampleInputs(5)

####################################################################################################
#       Run sample inputs and retrieve candidate equivalence set.
####################################################################################################
ansiCode.PrintOnThisLineBold("Preparing for concrete execution")
preExpr = [v.ComparisonToSmt() if depgraph.VertexNode.OpCode.IsComparison(v.operator) \
                               else v.VertexOperationToSmt() for v in preGraph.vertices]
preExpr = [x for x in preExpr if x != None]

# in dataRegionGraph, identify depgraph.VertexNode.VertexType.DATAREGION
# for each depgraph.VertexNode.VertexType.DATAREGION, group them by P1 or P2.
P1BoundTuple = []
P2BoundTuple = []
numP1Bounds = 0
numP2Bounds = 0

for drv in [dr for dr in dataRegionGraph.vertices if dr.type == depgraph.VertexNode.VertexType.DATAREGION] :
    if drv.programOrigin == "P1" :
        P1BoundTuple.append((drv.operands[1].VertexSubGraphToSmt(), drv.operands[2].VertexSubGraphToSmt()))
        numP1Bounds = numP1Bounds + 1
    elif drv.programOrigin == "P2" :
        P2BoundTuple.append((drv.operands[1].VertexSubGraphToSmt(), drv.operands[2].VertexSubGraphToSmt()))
        numP2Bounds = numP2Bounds + 1

boundTuplePermutations = itertools.permutations(P1BoundTuple, numP1Bounds)
mbsQueryList = []
for mb in boundTuplePermutations :
    mbQueryList = []
    for i in range(0, numP1Bounds-1) :
        mbQueryList.append(z3.ULT(mb[i][1], mb[i+1][0]))
    mbsQueryList.append(z3.And(mbQueryList))

preExpr.append(z3.Or(mbsQueryList))

for bt in P1BoundTuple :
    preExpr.append(z3.ULT(bt[0], bt[1]))

boundTuplePermutations = itertools.permutations(P2BoundTuple, numP2Bounds)
mbsQueryList = []
for mb in boundTuplePermutations :
    mbQueryList = []
    for i in range(0, numP2Bounds-1) :
        mbQueryList.append(z3.ULT(mb[i][1], mb[i+1][0]))
    mbsQueryList.append(z3.And(mbQueryList))

preExpr.append(z3.Or(mbsQueryList))

for bt in P2BoundTuple :
    preExpr.append(z3.ULT(bt[0], bt[1]))

programExpr = [x for x in map(lambda x : x.VertexOperationToSmt(), programGraph.vertices) if x != None]

###################################################
# Get a list of nodes we want to observe the values
varList = list(filter(lambda x : (x.type == depgraph.VertexNode.VertexType.VAR or \
                                  x.type == depgraph.VertexNode.VertexType.TEMP) and \
                                  x.bitlength >= 8, \
                            programGraph.vertices))
candiEquivSet = [list(varList)]
executedValueDict = {k : [] for k in varList}

###################################################
# Do Execution simulation.
for i, si in enumerate(sampGen.sampleInputs) :
    ansiCode.PrintOnThisLineBold("Concrete Execution %d/%d : " % ((i+1), len(sampGen.sampleInputs)))
    ansiCode.Print("Executing")
    modelDict = SymbolicExecAndGetModelDict(programExpr, preExpr, si, varList)
    ansiCode.PrintFromLeft("Retrieving values", 9)
    UpdateExecutedValueDict(executedValueDict, modelDict)
    ansiCode.PrintFromLeft("Refining", 17)
    candiEquivSet = RefineCandidateEquivSet(candiEquivSet, modelDict)


###################################################
# Detect if any of the variables evaluated to the same value for all executions
ansiCode.PrintOnThisLineBold("Performing post concrete execution analysis")
executedValueDict = {k : executedValueDict[k][0] for k in executedValueDict if AreAllElementsTheSame(executedValueDict[k])}

# If an element in candidate Equivalent Set has shown same value for all execution, we add the constant to the set.
for ceSet in candiEquivSet :
    if ceSet[0] in executedValueDict :
        # Must create a constant node for this list
        constantNode = depgraph.VertexNode()
        constantNode.operands = None
        constantNode.operator = depgraph.VertexNode.OpCode.NONE
        constantNode.value = executedValueDict[ceSet[0]].as_long()
        constantNode.name = None
        constantNode.index = None
        constantNode.programOrigin = None
        constantNode.type = depgraph.VertexNode.VertexType.IMM
        constantNode.bitlength = executedValueDict[ceSet[0]].size()
        constantNode.topRank = 0
        ceSet.append(constantNode)

        # The rest of the nodes in ceSet must be in executedValueDict as well
        for node in ceSet :
            executedValueDict.pop(node, None)

# If we have anything left in executedValueDict, it means that we have some nodes that are not in candidate equivalence sets. We create a new candidate equivalence set for each of these nodes and the constant corresponding to this node.
for k in executedValueDict :
    if executedValueDict[k] != None :
        constantNode = depgraph.VertexNode()
        constantNode.operands = None
        constantNode.operator = depgraph.VertexNode.OpCode.NONE
        constantNode.value = executedValueDict[k].as_long()
        constantNode.name = None
        constantNode.index = None
        constantNode.programOrigin = None
        constantNode.type = depgraph.VertexNode.VertexType.IMM
        constantNode.bitlength = executedValueDict[k].size()
        constantNode.topRank = 0
        candiEquivSet.append([constantNode, k])


###################################################
# Update the equivClassId in each candiEquivSet. Variables in each candiEquivSet must have "unique"
# equivClassId. While doing so, also convert it to a dictionary.
for i, ceSet in enumerate(candiEquivSet) :
    for v in ceSet : v.equivClassId = i
candiEquivSet = {k:v for k,v in enumerate(candiEquivSet)}

###################################################
# Determine if it's worth continuing to check whether the classified variables are equivalent
isWorthContinuing = True
for outEqVertex in postGraph.vertices :
    assert(outEqVertex.operator == depgraph.VertexNode.OpCode.EQ)
    if outEqVertex.operands[0].equivClassId == None or \
       outEqVertex.operands[1].equivClassId == None or \
       (outEqVertex.operands[0].equivClassId != outEqVertex.operands[1].equivClassId) :
        isWorthContinuing = False

if not isWorthContinuing :
    ansiCode.PrintOnThisLine("Performing post concrete execution analysis")
    ansiCode.Print("\n")
    ansiCode.PrintOnThisLineBold("%sp1 is not equivalent to p2 (Reason: Concrete Execution)\n" % (ansiCode.red))
    config.PrintStatistics()
    
else :
    ansiCode.PrintOnThisLine("Concrete execution finished\n")
    #################################################################################################
    #       Verify CandiEquivSet for specification program
    #################################################################################################
    ansiCode.PrintOnThisLineBold("Preparing to verify equivalence of nodes")
    for k,l in candiEquivSet.items() :
        assert(len(l) > 1)
        l.sort(key=lambda x: x.topRank)
    
    # In initial construction, take the first element of each set in specCandiEquivBucket.
    confEquivSet = {k:[l.pop(0)] for k,l in candiEquivSet.items()}

    # Get the list of vertices to find confirmed equivalence set, and sort them by topological rank.
    verticesToConfirm = list(reduce(lambda x, y : x + y, candiEquivSet.values(), []))
    verticesToConfirm.sort(key=lambda x: x.topRank)
    del candiEquivSet

    counter = 1
    numVerticesToConfirm = len(verticesToConfirm)
    config.totalNodesToCompare = numVerticesToConfirm
    config.equivNodeNum = 0
    config.noEquivNodeNum = 0
    config.readNodeNum = 0
    while verticesToConfirm != [] :
        ansiCode.PrintOnThisLineBold("Verifying node equiv #%d/%d (%s%d%s-%s%d%s)"
                                     % (counter, numVerticesToConfirm, ansiCode.green, config.equivNodeNum,
                                        ansiCode.black, ansiCode.red, config.noEquivNodeNum, ansiCode.black))
        nextVertex = verticesToConfirm.pop(0)

        verificationStartTime = time.time()
        programGraph, confEquivSet = \
          ClassifyVertexToConfEquivSet(nextVertex, programGraph, confEquivSet, preExpr, counter)
        config.totalVerificationTime = config.totalVerificationTime + (time.time() - verificationStartTime)
        
        counter = counter + 1
    del verticesToConfirm
    ansiCode.PrintOnThisLine("Verifying node equiv. finished\n")

    #################################################################################################
    #       Verify Output Variables are Equivalent
    #################################################################################################
    ansiCode.PrintOnThisLineBold("Determining equiv of p1 and p2")
    isImplEqToSpec = True
    for outEqVertex in postGraph.vertices :
        assert(outEqVertex.operator == depgraph.VertexNode.OpCode.EQ)
        if outEqVertex.operands[0] != outEqVertex.operands[1] : isImplEqToSpec = False

    if isImplEqToSpec :
        ansiCode.PrintOnThisLineBold("%sp1 is equivalent to p2\n" % (ansiCode.green))
        config.PrintStatistics()
    else :
        ansiCode.PrintOnThisLineBold("%sp1 is not equivalent to p2(Reason: Output semantically different)\n" % (ansiCode.red))
        config.PrintStatistics()
