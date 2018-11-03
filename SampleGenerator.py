import z3
import dslinstructions
import depgraph
import config
import ansiCode
import itertools

class SampleGenerator :
    def __init__(self, inPreGraph, inDataRegionGraph) :
        self.dataRegionGraph = inDataRegionGraph
        self.preGraph = inPreGraph
        self.preGraphExprList = None
        self.inputList = []
        
        ansiCode.Print("Identifying input variables")
        self.IdentifyInputs()
        #Calculate PreAst Expression in SMT
        self.SetPreAstExpr()
        #Calculate dataRegionExpression in SMT
        self.SetDataRegionExpr()

        self.inputCannotBeZeroExprList = None
        self.inputsAreDistinctExprList = None
        ansiCode.PrintFromLeft("Setting additional constraints", 27)
        self.SetAdditionalConstraintsForInputs()
        ansiCode.PrintFromLeft("", 27)
        self.sampleInputs = []

    # The precondition must contain all inputs in spec and asm
    # All inputs may not be used in spec/asm
    # However, all inputs must have one or more "buddy" = equivalent value.
    #
    # What do we consider as input?
    # 1) Variable = VertexNode.VertexType.VAR
    # 2) Array element = VertexNode.VertexType.TEMP && VertexNode.OpCode.LOAD
    #
    # Identify "inputs"
    def IdentifyInputs(self) :        
        self.inputList = []
        for v in self.preGraph.vertices :
            if v.type == depgraph.VertexNode.VertexType.VAR :
                self.inputList.append(v)
            elif v.type == depgraph.VertexNode.VertexType.TEMP and \
                 v.operator == depgraph.VertexNode.OpCode.LOAD :
                self.inputList.append(v)

        for drv in [dr for dr in self.dataRegionGraph.vertices if dr.type == depgraph.VertexNode.VertexType.DATAREGION] :
            if drv.operands[0] not in self.inputList :
                self.inputList.append(drv.operands[0])

        #####################################
        # Prune Constants from self.inputList
        for v in self.preGraph.vertices :
            if v.operator == depgraph.VertexNode.OpCode.EQ :
                if v.operands[0].type == depgraph.VertexNode.VertexType.IMM :
                    if v.operands[1] in self.inputList :
                        self.inputList.remove(v)
                if v.operands[1].type == depgraph.VertexNode.VertexType.IMM :
                    if v.operands[0] in self.inputList :
                        self.inputList.remove(v.operands[0])

    def SetAdditionalConstraintsForInputs(self) :
        # Input cannot be 0:
        self.SetInputCannotBeZeroExpr()
        # We want to make sure as many variables are distinct from each other,
        # but still adhere to preAstExpr:
        self.SetInputsAreDistinctExpr()

    def SetDataRegionExpr(self) :
        self.dataRegionExprList = []
        
        # in dataRegionGraph, identify depgraph.VertexNode.VertexType.DATAREGION
        # for each depgraph.VertexNode.VertexType.DATAREGION, group them by P1 or P2.
        P1BoundTuple = []
        P2BoundTuple = []
        numP1Bounds = 0
        numP2Bounds = 0

        for drv in [dr for dr in self.dataRegionGraph.vertices if dr.type == depgraph.VertexNode.VertexType.DATAREGION] :
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

        self.dataRegionExprList.append(z3.Or(mbsQueryList))

        for bt in P1BoundTuple :
            self.dataRegionExprList.append(z3.ULT(bt[0], bt[1]))

        boundTuplePermutations = itertools.permutations(P2BoundTuple, numP2Bounds)
        mbsQueryList = []
        for mb in boundTuplePermutations :
            mbQueryList = []
            for i in range(0, numP2Bounds-1) :
                mbQueryList.append(z3.ULT(mb[i][1], mb[i+1][0]))
            mbsQueryList.append(z3.And(mbQueryList))

        self.dataRegionExprList.append(z3.Or(mbsQueryList))

        for bt in P2BoundTuple :
            self.dataRegionExprList.append(z3.ULT(bt[0], bt[1]))

    def SetPreAstExpr(self) :
        # ToSmt() call on every vertex
        self.preAstExprList = \
        [x for x in
            [v.ComparisonToSmt() if depgraph.VertexNode.OpCode.IsComparison(v.operator)
            else v.VertexOperationToSmt()
            for v in self.preGraph.vertices]
        if x != None]
    
    def SetInputCannotBeZeroExpr(self) :
        assert(self.inputList != None)
        self.inputCannotBeZeroExprList = \
          list(map(lambda il : il.VertexNameToSmt() != z3.BitVecVal(0, il.bitlength), \
                   self.inputList))

    def SetInputsAreDistinctExpr(self) :
        # To make sure that not all inputs are exactly the same,
        # make sure as many of them are distinct.
        assert(self.preAstExprList != None)
        assert(self.dataRegionExprList != None)
        assert(self.inputCannotBeZeroExprList != None)
        self.inputsAreDistinctExprList = []
        # Add all "self.inputList[i] != self.inputList[j]" and look for satisfiability.
        # If sat, then we are done
        # If unsat, extract unsat core and remove all the unsat core term from
        # "self.inputList[i] != self.inputList[j]" list.
        
        self.inputsAreDistinctExprList = []
        for i in range(0, len(self.inputList) - 1) :
            for j in range(i + 1, len(self.inputList)) :
                if (self.inputList[i].bitlength == self.inputList[j].bitlength) :

                    # check that lhs and rhs are not the same
                    if self.inputList[i] == self.inputList[j] :
                        continue

                    # get user of i, check if any of them are depgraph.VertexNode.OpCode.EQ
                    addDistinct = True
                    for p in self.inputList[i].users :
                        if p.operator == depgraph.VertexNode.OpCode.EQ :
                            if p.operands[0] == self.inputList[i] and p.operands[1] == self.inputList[j] :
                                addDistinct = False
                                continue
                            if p.operands[0] == self.inputList[j] and p.operands[1] == self.inputList[i] :
                                addDistinct = False
                                continue

                    if addDistinct :              
                        lhs = self.inputList[i].VertexNameToSmt()
                        rhs = self.inputList[j].VertexNameToSmt()
                        expr = lhs != rhs
                        self.inputsAreDistinctExprList.append(expr)

        # z3 unsat_core does not necessarily retrieve every unsat_core.
        # So we must recursively run this.
        while True :
            s = z3.Solver()
            s.add(self.preAstExprList)
            s.add(self.dataRegionExprList)

            for i in range(0, len(self.inputCannotBeZeroExprList)) :
                if self.inputCannotBeZeroExprList[i] != None :
                    s.assert_and_track(self.inputCannotBeZeroExprList[i], "icbze" + str(i))
        
            for i in range(0, len(self.inputsAreDistinctExprList)) :
                if self.inputsAreDistinctExprList[i] != None :
                    s.assert_and_track(self.inputsAreDistinctExprList[i], "iadel" + str(i))
                    
            result = s.check()
            if (result.r == z3.Z3_L_TRUE) : break
            elif (result.r == z3.Z3_L_FALSE) :
                c = s.unsat_core()
                for i in range(0, len(self.inputsAreDistinctExprList)) :
                    if z3.Bool("iadel" + str(i)) in c :
                        self.inputsAreDistinctExprList[i] = None
                for i in range(0, len(self.inputCannotBeZeroExprList)) :
                    if z3.Bool("icbze" + str(i)) in c :
                        self.inputCannotBeZeroExprList[i] = None

        self.inputsAreDistinctExprList = list(filter(lambda x : x != None, \
                                                     self.inputsAreDistinctExprList))

        self.inputCannotBeZeroExprList = list(filter(lambda x : x != None, \
                                                     self.inputCannotBeZeroExprList))

    def CreateRandomSampleInput(self, seed) :
        assert(self.inputCannotBeZeroExprList != None)
        assert(self.inputsAreDistinctExprList != None)
        assert(self.preAstExprList != None)
        
        sampleInput = {}
        s = z3.Solver()
        z3.set_option("auto_config", False)
        z3.set_option("smt.phase_selection", 5)
        z3.set_option("smt.random_seed", seed)
        s.add(self.inputCannotBeZeroExprList)
        s.add(self.inputsAreDistinctExprList)
        s.add(self.preAstExprList)
        s.add(self.dataRegionExprList)

        s.check()
        currModel = s.model()
        
        for il in self.inputList :
            # Get value of the input variable
            if il.type == depgraph.VertexNode.VertexType.VAR :
                sampleInput[il] = currModel[il.VertexNameToSmt()]
            # Get value of the element in an input array
            elif il.type == depgraph.VertexNode.VertexType.TEMP and \
                 il.operator == depgraph.VertexNode.OpCode.LOAD :
                sampleInput[il] = currModel[il.VertexNameToSmt()]
        self.sampleInputs.append(sampleInput)

    def CreateRandomSampleInputs(self, numOfSamples) :
        for i in range(0, numOfSamples) :
            ansiCode.PrintOnThisLineBold("Generating sample inputs %d/%d" % (i + 1, numOfSamples))
            self.CreateRandomSampleInput(i)
