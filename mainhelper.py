import sys
import dslparse
import dslinstructions as di
import z3
import x86parse
import x86todsl
import x86todsl8bit
import depgraph
import config
import subprocess
import ansiCode
import time

# Reads file and returns the string representation of it.
def readFile(fileName) :
    myFile = open(fileName, 'r')
    retString = myFile.read()
    myFile.close()
    return retString

def ParseProgramToDsl(programString, plang, progPrefix) :
    if plang == 0 : return ParseSpecStringToDsl(programString, progPrefix)
    elif plang == 1 : return ParseAsmStringToDSL(programString, progPrefix)
    else :
        print()
        sys.exit("Unknown code for config.p1lang = %d" % (plang))

# Reads the spec string and turn it into Dsl. Each DslInstruction class will contain one instruction.
def ParseSpecStringToDsl(specString, progOrig) :
    # Parse dsl program string
    specAst = dslparse.dslToAst(specString)
    # Separate out function definitions and other parts.
    functions, specAst = ProcessFunctions(specAst)
    # Inline the function calls with function definition.
    replaceFunctions(functions, specAst)
    # Unroll Loops
    specAst = UnrollLoops(specAst)
    
    # Once replaced, see if it's a "memory" store or load.
    for sa in specAst :
        if isinstance(sa.lhs, di.ArrayCall) and sa.comparator == "=" :
            sa.comparator = "<-"

    # Set programOrigin.
    for sa in specAst :
        sa.SetProgramOrigin(progOrig, False)

    return specAst

def ProcessFunctions(dslAst) :
    functions = {}
    retDslAst = []
    for da in dslAst :
        if isinstance(da, di.Function) or isinstance(da, di.Macro) :
            functions[da.name] = da
        else :
            retDslAst.append(da)
    return functions, retDslAst

def replaceFunctions(functions, ast) :
    i = 0
    while i < len(ast) :
        da = ast[i]
        retVal = da.ReplaceFunction(functions)
        if retVal != None :
            ast[i:i+1] = retVal
            i = i - 1
        i = i + 1

# Read the asm strings, parse each asm instruction and translate to dsl instructions.
def ParseAsmStringToDSL(asmString, progOrigin) :
    # Remove comments: double slash stuff.
    asmStringList = asmString.splitlines()
    asmStringList = list(map((lambda x: OneLineRemoveComment(x).strip()), asmStringList))
    asmStringList = list(filter((lambda x: x != ""), asmStringList))
    finalString = ""
    for asl in asmStringList :
        finalString = finalString + asl + "\n"

    # Parse asmString using pyparsing
    insts = x86parse.ASMToX86Parse(finalString)

    # Convert asm instructions into DSL instructions
    x86Dsl = None
    if config.memModel == 32 :
        x86Dsl = x86todsl.ConvertToDsl(insts)
    elif config.memModel == 8 :
        x86Dsl = x86todsl8bit.ConvertToDsl(insts)

    for xd in x86Dsl :
        xd.SetProgramOrigin(progOrigin, False)
    
    return x86Dsl

# Function that removes everything after '//' token (which are comments)
def OneLineRemoveComment(s) :
    commentIndex = s.find('//')
    if commentIndex < 0 :
        return s
    return s[:commentIndex]

# Unrolls dsl that may have loops to a straight line code.
# Return value: A list of dslinstructions that represent a straight line code.
def UnrollLoops(progInDsl) :
    progState = {}
    progState["lineNum"] = 0
    retList = []
    oneBasicBlock = GetNextBasicBlock(progInDsl, progState)
    while oneBasicBlock != [] :
        retList = retList + oneBasicBlock
        oneBasicBlock = GetNextBasicBlock(progInDsl, progState)
    
    return retList

# Gets the next basic block (iteration) based on the state of dslProgState
# Return value: a list of dslinstructions that represent a basic block
def GetNextBasicBlock(progInDsl, progState) :
    retList = []
    if len(progInDsl) == 0 :
        return []

    while progState["lineNum"] < len(progInDsl) :
        inst = progInDsl[progState["lineNum"]]
        if not isinstance(inst, di.Loop) :
            # If it's not a loop, add the instruction to the return List.
            newInst = inst.Copy()
            retList.append(newInst)
            progState["lineNum"] = progState["lineNum"] + 1
    
        if isinstance(inst, di.Loop) :
            if len(retList) > 0 :
                # If there's something in the return List, then return what we have.
                return retList
            if inst.i not in progState :
                # lp.i = initiate the index value
                progState[inst.i] = inst.lb
            else :
                # lp.i = increment the index value
                progState[inst.i] = progState[inst.i] + 1

            if progState[inst.i] > inst.ub :
                # if lp.i > lp.ub, then we no longer need to iterate through this for loop.
                progState.pop(inst.i, None)
                progState["lineNum"] = progState["lineNum"] + 1
                continue
            
            if len(inst.expr) == 0 :
                # If the for loop is empty, then we have nothing to do in this for loop.
                progState["lineNum"] = progState["lineNum"] + 1
                continue
            
            iVal = progState[inst.i]
            for stmt in inst.expr :
                # For each statement in the for loop, replace index variable to the concrete value
                # Add the new statement to the return List
                newStmt = stmt.Copy()
                newStmt.FindAndReplace(inst.i, iVal)
                retList.append(newStmt)
            return retList
    return retList

# Look for uses of array. If the array is only stored/accessed using constants, we can inline them.
def InlineArrayAccesses(preAst, specAst, postAst) :
    arrIndexOnlyConstDict = {}
    for inst in preAst :
        inst.AnalyzeArrayIndexOnlyConst(arrIndexOnlyConstDict)
    for inst in specAst :
        inst.AnalyzeArrayIndexOnlyConst(arrIndexOnlyConstDict)
    for inst in postAst :
        inst.AnalyzeArrayIndexOnlyConst(arrIndexOnlyConstDict)    

    arrToInlineList = []
    for k, v in arrIndexOnlyConstDict.items() :
        if v == True : arrToInlineList.append(k)
    del arrIndexOnlyConstDict

    for inst in preAst :
        inst.InlineArrayReadWrite(arrToInlineList)
    for inst in specAst :
        inst.InlineArrayReadWrite(arrToInlineList)
    for inst in postAst :
        inst.InlineArrayReadWrite(arrToInlineList)

def ConvertToSSAForms(preAst, specAst, asmAst, postAst) :
    ssaState = {}
    ToSSA(preAst, ssaState, False)
    ToSSA(specAst, ssaState)
    ToSSA(asmAst, ssaState)
    ToSSA(postAst, ssaState, False)
    RemoveUndefinedInstruction(asmAst)


def ToSSA(dslAst, indexMapping, updateIndex = True) :
    for da in dslAst :
        da.UpdateSsaIndex(indexMapping, updateIndex)


# For assembly, in order to express "undefinedness" of a register, we use the form
# reg = builtin_undef.
# Once the instructions are turned to SSA form, then we can simply remove such instruction,
# as "reg" will be an unbounded variable thereafter.
def RemoveUndefinedInstruction(ast) :
    ast[:] = [aa for aa in ast if not isinstance(aa, di.Statement) or \
                                  not isinstance(aa.lhs, di.Variable) or \
                                  not isinstance(aa.rhs, di.Variable) or \
                                  aa.rhs.name != "builtin_undef"]

def ConstantPropagate(ast) :
    for inst in ast :
        inst.ConstantPropagate()

def ExtractDataRegions(preAst) :
    dataRegions = [pa for pa in preAst if isinstance(pa, di.DataRegion)]
    preAst = [pa for pa in preAst if not isinstance(pa, di.DataRegion)]
    return preAst, dataRegions

def GetGraphsFromAsts(dataRegionAst, preAst, specAst, asmAst, postAst) :

    ###########################
    # Create dataRegion graph
    ansiCode.Print("data region")
    dataRegionGraph = depgraph.DepGraph("dataRegion")
    for dr in dataRegionAst :
        dataRegionGraph.AddDslInstruction(dr, [])
    
    ###########################
    # Create precondition graph
    ansiCode.Print("%s%spre condition" % (ansiCode.Left(11), ansiCode.ClearLine(0)))
    preGraph = depgraph.DepGraph("preTempName")
    for pa in preAst :
        preGraph.AddDslInstruction(pa, [])

    ##########################
    # Create Spec + Impl Graph
    ansiCode.Print("%s%sp1" % (ansiCode.Left(13), ansiCode.ClearLine(0)))
    programGraph = depgraph.DepGraph("P1TempName")
    for sa in specAst :
        programGraph.AddDslInstruction(sa, [])
    ansiCode.Print("%s%sp2" % (ansiCode.Left(2), ansiCode.ClearLine(0)))
    programGraph.tempName = "P2TempName"
    for aa in asmAst :
        programGraph.AddDslInstruction(aa, [])

    variables = list(filter(lambda x : x.type == depgraph.VertexNode.VertexType.VAR or \
                                                   x.type == depgraph.VertexNode.VertexType.ARR, \
                                        programGraph.vertices))

    

    #############################
    # Create post condition graph
    ansiCode.Print("%s%spost condition" % (ansiCode.Left(2), ansiCode.ClearLine(0)))
    postGraph = depgraph.DepGraph("postTempName")
    for pa in postAst :
        postGraph.AddDslInstruction(pa, variables)

    # Identify all "progOutput." progOutput are the nodes used in final "==" comparison.
    for v in postGraph.vertices :
        if depgraph.VertexNode.VertexType.IsVarOrTemp(v.type) and \
           v.operator == depgraph.VertexNode.OpCode.EQ and v.users == None :
            # There are two operands: left side and right side. Mark both of them as progOutput
            v.operands[0].AddMetadata("progOutput", True)
            v.operands[1].AddMetadata("progOutput", True)
            v.AddMetadata("finalComp", True)

    # Clean variables list.
    variables.clear()
    del variables
    
    # Nodes between preGraph, programGraph, and postGraph are all shared. I don't know if it's the
    # best way of doing it... but, we will go ahead with it for now.

    # We move nodes from postGraph to programGraph. We move all expression DAGS to programGraph. In
    # the end, postGraph should only have "var1 == var2" graphs.
    # Example: if postGraph has "a + b == c", then, postGraph will have nodes "a", "b",
    # "postTempName1 = a + b", and "postTempName1 == c". We move "a", "b", "postTempName1 = a + b"
    # nodes to preGraph/programGraph, and only keep "postTempName1 == c"

    ###########################################
    # Move nodes from postGraph to programGraph
    ansiCode.Print("%s%sOrganizing nodes" % (ansiCode.Left(14), ansiCode.ClearLine(0)))
    for v in list(postGraph.vertices) :
        if "finalComp" not in v.metadata :
            postGraph.vertices.remove(v)
            if not v in programGraph.vertices :
                programGraph.vertices.insert(0, v)

    ########################################################
    # Resolve "assign" nodes. Get rid of all "assign" nodes.
    for v in programGraph.vertices :
        if v.operator == depgraph.VertexNode.OpCode.ASSIGN :
            assert(v.type == depgraph.VertexNode.VertexType.VAR or \
                   v.type == depgraph.VertexNode.VertexType.TEMP)
            assert(v.operands != None and len(v.operands) == 1)
            depgraph.DepGraph.ReplaceVertex(v, v.operands[0])

    ############
    # Reduce DAG
    ansiCode.Print("%s%sReducing DAGs" % (ansiCode.Left(16), ansiCode.ClearLine(0)))
    ReduceProgramGraph(programGraph)

    ###############################
    # Caclualte Topological Ranking
    ansiCode.Print("%s%sCalculating topological ranking" % (ansiCode.Left(13), ansiCode.ClearLine(0)))
    CalculateTopologicalRanking(programGraph)
    
    return dataRegionGraph, preGraph, programGraph, postGraph
    
def ReduceProgramGraph(programGraph) :
    listOfProgOutput = [x for x in programGraph.vertices if "progOutput" in x.metadata]
    for po in listOfProgOutput :
        AddMetadataToSelfAndAllOperands(po, "marked", True)

    for v in [x for x in programGraph.vertices if "marked" not in x.metadata] :
        v.CutAllTies()
        programGraph.vertices.remove(v)

    for po in listOfProgOutput :
        RemoveMetadataToSelfAndAllOperands(po, "marked")

def AddMetadataToSelfAndAllOperands(v, meta, val) :
    if meta in v.metadata : return
    v.AddMetadata(meta, val)
    if v.operands == None : return
    for op in v.operands :
        if op != None : AddMetadataToSelfAndAllOperands(op, meta, val)

def RemoveMetadataToSelfAndAllOperands(v, meta) :
    if not meta in v.metadata : return
    v.RemoveMetadata(meta)
    if v.operands == None : return
    for op in v.operands :
        if op != None : RemoveMetadataToSelfAndAllOperands(op, meta)

def SymbolicExecAndGetModelDict(programExpr, precondExpr, sampleInput, varList) :
    sampleInputExpr = z3.And(list(map(lambda k : k.VertexNameToSmt() == sampleInput[k], \
                                      sampleInput.keys())))
    s = z3.Solver()
    z3.reset_params()
    s.add(precondExpr)
    s.add(programExpr)
    s.add(sampleInputExpr)
    
    s.check()
    model = s.model()
    return {v:model[v.VertexNameToSmt()] for v in varList}

def UpdateExecutedValueDict(executedValueDict, modelDict) :
    for evk in executedValueDict :
        executedValueDict[evk].append(modelDict[evk])

def AreAllElementsTheSame(lst) :
    iterator = iter(lst)
    try:
        first = next(iterator)
    except StopIteration:
        return True
    return all(first == rest for rest in iterator)

# candiEquivSet = candidate equivalent set.
# sampleResult = is the new model for a new sample.
# Refine candiEquivSet using the new sampleResult.
def RefineCandidateEquivSet(candiEquivSet, sampleResult) :
    newCandiEquivSet = []
    for ces in candiEquivSet :
        # For each equivalent set, split the set into smaller sets
        # depending on the new sampleResult values.
        tempDictBucket = {}
        for el in ces :
            AddToDictBucket(tempDictBucket, sampleResult[el], el)
        # Once it is split, identify the sets that have more than one element,
        # and add it to the newCandiEquivSet
        for key in tempDictBucket :
            if len(tempDictBucket[key]) > 1 :
                newCandiEquivSet.append(tempDictBucket[key])
    return newCandiEquivSet

# Add el into the key in DictBucket
def AddToDictBucket(dictBucket, key, el) :
    if key == None :
        # Then el can be ANYTHING. In this case, we do not include it in CandidateEquivalenceSet.
        return
    if (key, key.size()) not in dictBucket :
        dictBucket[(key, key.size())] = []
    if el not in dictBucket[(key, key.size())] :
        dictBucket[(key, key.size())].append(el)

def CalculateTopologicalRanking(graph) :
    # We will take every vertex, and calculate topological ranking.
    for v in graph.vertices : v.CalculateTopRank()

# Input
#   vertex1 : a temporary/variable vertex
#   vertex2 : a temporary/variable vertex where vertex2 != vertex1
#   baseGraph : the dependency graph of a program
#
# Output
#   Creates a minimal subgraph of baseGraph, where the outputs are vertex1 and vertex2.
#   The minimal subgraph contains a copy of the vertices in baseGraph. Therefore, changing the
#   vertices in the minimal subgraph will not change any vertex in baseGraph.
#   
def CalculateMinimalRelationalSubGraph(vertex1, vertex2) :    
    AddMetadataToSelfAndAllOperands(vertex1, "red", True)
    AddMetadataToSelfAndAllOperands(vertex2, "blue", True)
    CalculateMRSGVertices(vertex1, vertex2)

def CalculateMRSGVertices(vertex1, vertex2) :
    CalculateMRSGVertex(vertex1)
    CalculateMRSGVertex(vertex2)

def CalculateMRSGVertex(vertex) :
    if "MRSG_Analyzed" in vertex.metadata : return
    assert("red" in vertex.metadata or "blue" in vertex.metadata)

    if ("red" in vertex.metadata) ^ ("blue" in vertex.metadata) :
        vertex.AddMetadata("MRSG", True)
    # Otherwise, vertex is both "red" and "blue" = "purple"
    else :
        assert(vertex.users != None)
        for usr in vertex.users :
            if ("red" in usr.metadata) ^ ("blue" in usr.metadata) :
                vertex.AddMetadata("MRSG", True)
                break

    vertex.AddMetadata("MRSG_Analyzed", True)
    if "MRSG" not in vertex.metadata : return
    # Check if the operands are "MRSG" vertex
    if vertex.operands == None : return
    for op in vertex.operands :
        # If vertex is "MRSG" node, and op is VertexType.FUNC or VertexType.IMM,
        # they're "MRSG" as well:
        if op.type == depgraph.VertexNode.VertexType.FUNC : op.AddMetadata("MRSG", True)
        elif op.type == depgraph.VertexNode.VertexType.IMM : op.AddMetadata("MRSG", True)
        else : CalculateMRSGVertex(op)
    return

    
def DeleteMetadatasFromGraph(graph, metadatas) :
    for v in graph.vertices :
        for md in graph.vertices :
            v.RemoveMetadata(md)

# From this read node, walk down the graph
# For every write node, determine def, maybe, and not
# Goal: Narrow the scope of array read (to only include indexes/values it may read)
# Implementation: Let's use conditional nodes to do this for now.
# (1) maybe: create if (read index == write index) then (write value) else (empty).
# (2) def: fill (empty) with (write value), stop and return.
# (3) not: skip this node and keep going.
# (4) initial array: fill (empty) with initialArray[read index], stop and return.
def ReduceThisArrayRead(vertex, graph, addtlExprs) :
    # Helper function to add newly created vertices to graph.
    def AddVertexAndDescendantsToGraph(node, graph) :
        if "NotInGraph" not in node.metadata : return
        # It's created in this function. We should add it to graph.vertices
        graph.vertices.insert(0, node)
        node.RemoveMetadata("NotInGraph")
        if node.operands == None : return
        for op in node.operands :
            AddVertexAndDescendantsToGraph(op, graph)
        
    # Make sure this vertex is array read node.
    assert(vertex.operator == depgraph.VertexNode.OpCode.LOAD)

    # (1) Simplest case : If vertex accesses from initial array, then we dont do anything.
    if vertex.operands[0].operator == depgraph.VertexNode.OpCode.NONE and \
       vertex.operands[0].type == depgraph.VertexNode.VertexType.ARR : return vertex

    newValueRoot = depgraph.VertexNode()
    newValueRoot.operator = depgraph.VertexNode.OpCode.NONE
    newValueRoot.name = "reducedReadNode"
    newValueRoot.index = graph.GetNextNameIndex()
    newValueRoot.type = depgraph.VertexNode.VertexType.NONE
    newValueRoot.AddMetadata("NotInGraph", True)
    newValueRoot.topRank = vertex.topRank
    newValueRoot.equivClassId = vertex.equivClassId
    currentHole = newValueRoot

    thisReadIndex = vertex.operands[1]
    iterator = vertex.operands[0]
    config.readNodeNum = config.readNodeNum + 1
    config.indexAliasNum = 0
    while iterator.operands != None :
        arrayWriteIndex = iterator.operands[1]
        arrayWriteValue = iterator.operands[2]
        config.indexAliasNum = config.indexAliasNum + 1
        config.totalIndexAliasNum = config.totalIndexAliasNum + 1
        ansiCode.PrintOnThisLine("  Reducing read node #%d: alias #%d" % (config.readNodeNum, config.indexAliasNum))

        # If arrayWriteIndex and thisReadIndex is both IMM, then just compare. In this case, there
        # is only def-alias and not-alias.
        if arrayWriteIndex.type == depgraph.VertexNode.VertexType.IMM and \
           thisReadIndex.type == depgraph.VertexNode.VertexType.IMM :
            if arrayWriteIndex.value == thisReadIndex.value :
                depgraph.DepGraph.ReplaceVertex(currentHole, arrayWriteValue)
                if newValueRoot == currentHole : newValueRoot = arrayWriteValue
                currentHole = arrayWriteValue
                depgraph.DepGraph.ReplaceVertex(vertex, newValueRoot)
                AddVertexAndDescendantsToGraph(newValueRoot, graph)
                return newValueRoot
            else :
                iterator = iterator.operands[0]
                continue

        # Check if arrayWriteIndex def-alias with thisReadIndex.
        # If arrayWriteIndex and thisReadIndex are not both immediate, then we should have verified
        # the equivalence between these two nodes already.
        # TODO : Verify equivalence between immediate nodes and var/temp nodes.
        if depgraph.VertexNode.VertexType.IsVarOrTemp(arrayWriteIndex.type) and \
           depgraph.VertexNode.VertexType.IsVarOrTemp(thisReadIndex.type) :
            # In this case, the two index definitely aliases if they are the same nodes.
            if arrayWriteIndex == thisReadIndex :
                depgraph.DepGraph.ReplaceVertex(currentHole, arrayWriteValue)
                if newValueRoot == currentHole : newValueRoot = arrayWriteValue
                currentHole = arrayWriteValue
                depgraph.DepGraph.ReplaceVertex(vertex, newValueRoot)
                AddVertexAndDescendantsToGraph(newValueRoot, graph)
                return newValueRoot
        else :
            check = VerifyEquivalent(arrayWriteIndex, thisReadIndex, graph, addtlExprs)
            if check == "unsat" :
                depgraph.DepGraph.ReplaceVertex(currentHole, arrayWriteValue)
                if newValueRoot == currentHole : newValueRoot = arrayWriteValue
                currentHole = arrayWriteValue
                depgraph.DepGraph.ReplaceVertex(vertex, newValueRoot)
                AddVertexAndDescendantsToGraph(newValueRoot, graph)
                return newValueRoot
            elif check == "unknown" :
                config.currentUnknownCount = config.currentUnknownCount + 1
                if config.currentUnknownCount >= config.maxUnknownCount :
                    config.analysisEndTime = time.time()
                    ansiCode.Print("\n")
                    ansiCode.PrintOnThisLineBold("%sp1 is not equivalent to p2 (Reason: SMT Timeout)\n" % (ansiCode.red))
                    config.PrintStatistics()
                    config.PrintGout("p1 is not equivalent to p2 (Reason: SMT Timeout)")
                    sys.exit("")

        # Check if it maybe aliases
        check = VerifyMayAlias(arrayWriteIndex, thisReadIndex, graph, addtlExprs)
        if check == "sat":
            # Create equality compare node
            tempCmpNode = depgraph.VertexNode()
            tempCmpNode.operands = [arrayWriteIndex, thisReadIndex]
            for op in tempCmpNode.operands :
                if op.users == None : op.users = []
                op.users.append(tempCmpNode)
            tempCmpNode.operator = depgraph.VertexNode.OpCode.EQ
            tempCmpNode.value = None
            tempCmpNode.name = "reducedReadNode"
            tempCmpNode.index = graph.tempNameCounter
            graph.tempNameCounter = graph.GetNextNameIndex()
            tempCmpNode.bitlength = -1 # Compare is a boolean. bitlength does not exist.
            tempCmpNode.type = depgraph.VertexNode.VertexType.TEMP
            tempCmpNode.AddMetadata("NotInGraph", True)


            # Create new hole.
            newHole = depgraph.VertexNode()
            newHole.operator = depgraph.VertexNode.OpCode.NONE
            newHole.name = "reducedReadNode"
            newHole.index = graph.GetNextNameIndex()
            newHole.type = depgraph.VertexNode.VertexType.NONE
            newHole.AddMetadata("NotInGraph", True)
            newHole.topRank = currentHole.topRank - 1

            # Fill currentHole with Conditional Assignment node.
            currentHole.operands = [tempCmpNode, arrayWriteValue, newHole]
            for op in currentHole.operands :
                if op.users == None : op.users = []
                op.users.append(currentHole)
            currentHole.operator = depgraph.VertexNode.OpCode.CONDITIONAL
            currentHole.value = None
            currentHole.type = depgraph.VertexNode.VertexType.TEMP
            currentHole.bitlength = arrayWriteValue.bitlength
            currentHole.AddMetadata("NotInGraph", True)

            # Update currentHole to the newHole.
            currentHole = newHole

        elif check == "unknown" :
            config.currentUnknownCount = config.currentUnknownCount + 1
            if config.currentUnknownCount >= config.maxUnknownCount :
                config.analysisEndTime = time.time()
                ansiCode.Print("\n")
                ansiCode.PrintOnThisLineBold("%sp1 is not equivalent to p2 (Reason: SMT Timeout)\n" % (ansiCode.red))
                config.PrintStatistics()
                config.PrintGout("p1 is not equivalent to p2 (Reason: SMT Timeout)")
                sys.exit("")

        
        # There is no aliasing. Keep looking at the next ones.
        iterator = iterator.operands[0]
        
    # The fact that we reached here, means there was no def-alias. We fill the hole with array read
    # node using initial array and thisReadIndex.
    currentHole.operands = [iterator, thisReadIndex]
    for op in currentHole.operands :
        if op.users == None : op.users = []
        op.users.append(currentHole)
    currentHole.operator = depgraph.VertexNode.OpCode.LOAD
    currentHole.type = depgraph.VertexNode.VertexType.TEMP
    currentHole.bitlength = iterator.arrayElBitlength
    depgraph.DepGraph.ReplaceVertex(vertex, newValueRoot)
    AddVertexAndDescendantsToGraph(newValueRoot, graph)
    return newValueRoot
    
def FindArrayAccessFromAncestors(vertex) :
    arrayAccessList = []
    verticesToCheck = [vertex]
    while verticesToCheck != [] :
        nextVertex = verticesToCheck.pop(0)
        # If already analyzed, all its ancestors are analyzed too.
        if "aaa" in nextVertex.metadata : continue

        # If it's a LOAD, add to arrayAccessSet.
        if nextVertex.operator == depgraph.VertexNode.OpCode.LOAD :
            if not nextVertex in arrayAccessList :
                arrayAccessList.append(nextVertex)

        # In any way, add "aaa" (array access analyzed) = True, and look at its operands
        nextVertex.AddMetadata("aaa", True)
        if nextVertex.operands == None : continue
        for op in nextVertex.operands : verticesToCheck.append(op)
    return arrayAccessList

# Vertex is any kind of node.
# This function finds all array read nodes that are descendants of vertex.
def ReduceDescendantArrayReadOfVertex(vertex, graph, ces, addtlExprs) :
    arrayReadList = FindArrayAccessFromAncestors(vertex)
    if arrayReadList == [] :
        return vertex
    arrayReadList.sort(key=lambda x: x.topRank)

    for ar in arrayReadList :
        # Reduce array read node (ar).
        newVertex = ReduceThisArrayRead(ar, graph, addtlExprs)

        # if ces is not None and ar exists in ces, then replace ar with newVertex
        if ces != None :
            for key, ce in ces.items() :
                for i in range(0, len(ce)) :
                    if ce[i] == ar : ce[i] = newVertex
        
        if (ar == vertex) and (newVertex != vertex) : vertex = newVertex
    return vertex

def ExecuteBashZ3FromSolver(s) :
    f = open(config.tempQueryFile, "w")
    f.write(s.sexpr())
    f.write("\n" + config.z3CheckSatCommand)
    f.close()

    smtStartTime = time.time()
    proc = subprocess.Popen(["../z3-master/build/z3", config.tempQueryFile], stdout=subprocess.PIPE)
    output = proc.stdout.readline()
    output = output.decode('ascii').rstrip()
    config.totalSmtTime = config.totalSmtTime + (time.time() - smtStartTime)
    return output

def ExecuteZ3PyFromSolver(s) :
    smtStartTime = time.time()
    check = s.check()
    config.totalSmtTime = config.totalSmtTime + (time.time() - smtStartTime)
    if check == z3.unsat : return "unsat"
    elif check == z3.sat : return "sat"
    elif check == z3.unknown : return "unknown"
    else :
        sys.exit("Z3Py answer unexpected : %s" % (check))

def VerifyEquivalentDefaultMode(v1, v2, graph, addtlExprs) :
    AddMetadataToSelfAndAllOperands(v1, "MRSG", True)
    AddMetadataToSelfAndAllOperands(v2, "MRSG", True)
    
    mrsgExpr = []
    for v in graph.vertices :
        if "MRSG" in v.metadata :
            tempExpr = v.VertexOperationToSmt()
            if tempExpr != None : mrsgExpr.append(tempExpr)

    RemoveMetadataToSelfAndAllOperands(v1, "MRSG")
    RemoveMetadataToSelfAndAllOperands(v2, "MRSG")

    z3.set_option(timeout=config.smtTimeout)
    s = z3.Solver()

    s.add(addtlExprs)
    s.add(mrsgExpr)
    s.add(v1.VertexNameToSmt() != v2.VertexNameToSmt())

    return ExecuteZ3PyFromSolver(s)
    
    
def VerifyEquivalentIntersectionMode(v1, v2, graph, addtlExprs) :
    CalculateMinimalRelationalSubGraph(v1, v2)
    mrsgExpr = []
    
    for v in graph.vertices :
        if not "MRSG" in v.metadata : continue
        isUnbound = False
        if v.operands == None : isUnbound = True
        else :
            for op in v.operands :
                if op.type == depgraph.VertexNode.VertexType.FUNC : continue
                if op.type == depgraph.VertexNode.VertexType.IMM : continue
                if not "MRSG" in op.metadata :
                    isUnbound = True
                    break

        if not isUnbound :
            tempExpr = v.VertexOperationToSmt()
            if tempExpr != None : mrsgExpr.append(tempExpr)

    RemoveMetadataToSelfAndAllOperands(v1, "MRSG")
    RemoveMetadataToSelfAndAllOperands(v1, "red")
    RemoveMetadataToSelfAndAllOperands(v1, "blue")
    RemoveMetadataToSelfAndAllOperands(v1, "MRSG_Analyzed")
    RemoveMetadataToSelfAndAllOperands(v2, "MRSG")
    RemoveMetadataToSelfAndAllOperands(v2, "red")
    RemoveMetadataToSelfAndAllOperands(v2, "blue")
    RemoveMetadataToSelfAndAllOperands(v2, "MRSG_Analyzed")

    z3.set_option(timeout=config.smtTimeout)
    s = z3.Solver()

    s.add(addtlExprs)
    s.add(mrsgExpr)
    s.add(v1.VertexNameToSmt() != v2.VertexNameToSmt())

#    if config.equivNodeNum == 358 :
#        print(s.sexpr())
#        sys.exit("")

    return ExecuteZ3PyFromSolver(s)

            
def VerifyEquivalent(v1, v2, graph, addtlExprs, dolog = False, compNumber = 0) :
    # Depending on verifMode configuration, act differently
    if config.verifMode == 1 :
        # Do default verification
        return VerifyEquivalentDefaultMode(v1, v2, graph, addtlExprs)
    elif config.verifMode == 2 :
        # Do intersection verification
        return VerifyEquivalentIntersectionMode(v1, v2, graph, addtlExprs)
    elif config.verifMode == 3 :
        # Do intersection -> if not unsat, then default
        result = VerifyEquivalentIntersectionMode(v1, v2, graph, addtlExprs)
        if result != "unsat" :
            result = VerifyEquivalentDefaultMode(v1, v2, graph, addtlExprs)
        return result

def VerifyMayAlias(v1, v2, graph, addtlExprs) :
    AddMetadataToSelfAndAllOperands(v1, "MRSG", True)
    AddMetadataToSelfAndAllOperands(v2, "MRSG", True)
    
    mrsgExpr = []
    for v in graph.vertices :
        if "MRSG" in v.metadata :
            tempExpr = v.VertexOperationToSmt()
            if tempExpr != None : mrsgExpr.append(tempExpr)

    RemoveMetadataToSelfAndAllOperands(v1, "MRSG")
    RemoveMetadataToSelfAndAllOperands(v2, "MRSG")

    z3.set_option(timeout=config.smtTimeout)
    s = z3.Solver()
    s.add(addtlExprs)
    s.add(mrsgExpr)
    s.add(v1.VertexNameToSmt() == v2.VertexNameToSmt())

    # 8, 1
#    if config.readNodeNum == 8 and config.indexAliasNum == 1 :
#        print(s.sexpr())
#        sys.exit("")
    
    return ExecuteZ3PyFromSolver(s)

# Given a vertex and confEquivSet, classifies vertex in confEquivSet.
# Also, cleans the graph accordingly if an equivalence set is found.
def ClassifyVertexToConfEquivSet(v2, graph, confEquivSet, addtlExprs, compNumber) :
    assert(v2.equivClassId in confEquivSet)
    
    compareAgainst = [x for x in confEquivSet[v2.equivClassId]]
    for v1 in compareAgainst :
            
        # Remove array read node in v1 and v1's descendants
        if config.aliasAnalysis :
            ansiCode.Print("\n")
            aliasAnalysisStartTime = time.time()
            v1 = ReduceDescendantArrayReadOfVertex(v1, graph, confEquivSet, addtlExprs)
            v2 = ReduceDescendantArrayReadOfVertex(v2, graph, confEquivSet, addtlExprs)
            config.totalAliasAnalysisTime = config.totalAliasAnalysisTime + (time.time() - aliasAnalysisStartTime)
            ansiCode.Print("%s%s%s" % (ansiCode.Left(1000), ansiCode.ClearLine(0), ansiCode.Up(1)))

        # If they are the same node, return.
        if v1 == v2 :
            config.equivNodeNum = config.equivNodeNum + 1
            return graph, confEquivSet

        # Check equivalence of v1 and v2.
        check = VerifyEquivalent(v1, v2, graph, addtlExprs, True, compNumber)
        # If they are equivalent, add v1 to confEquivSet, and change graph accordingly.
        if check == "unsat" :
            # If both of them are VAR/TEMP, then we use ReplaceVertex
            if depgraph.VertexNode.VertexType.IsVarOrTemp(v1.type) and \
               depgraph.VertexNode.VertexType.IsVarOrTemp(v2.type) :
                depgraph.DepGraph.ReplaceVertex(v2, v1)
            else :
                assert(v1.type == depgraph.VertexNode.VertexType.IMM or \
                       v2.type == depgraph.VertexNode.VertexType.IMM)
                depgraph.DepGraph.ReplaceVertex(v2, v1)
            config.equivNodeNum = config.equivNodeNum + 1
            return graph, confEquivSet
        elif check == "unknown" :
            config.currentUnknownCount = config.currentUnknownCount + 1
            if config.currentUnknownCount >= config.maxUnknownCount :
                config.analysisEndTime = time.time()
                ansiCode.Print("\n")
                ansiCode.PrintOnThisLineBold("%sp1 is not equivalent to p2 (Reason: SMT Timeout)\n" % (ansiCode.red))
                config.PrintStatistics()
                config.PrintGout("p1 is not equivalent to p2 (Reason: SMT Timeout)")
                sys.exit("")

        # else do nothing!
                
    # If none of them are equivalent, add v2 to confEquivSet.
    confEquivSet[v2.equivClassId].append(v2)
    config.noEquivNodeNum = config.noEquivNodeNum + 1
    return graph, confEquivSet
