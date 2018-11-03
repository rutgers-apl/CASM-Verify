from enum import Enum
import dslinstructions as di
import z3

class DepGraph() :
    def __init__(self, inTempName = "tempName") :
        self.vertices = []
        self.tempNameCounter = 0
        self.tempName = inTempName

    def AddDslInstruction(self, inst, extVars) :
        # Convert DSL instruction into dependency graph and add them.
        self.AddDslInstructionHelper(inst, extVars)

    def AddDslInstructionHelper(self, inst, extVars) :
        if isinstance(inst, di.Variable): return self.CreateVertexVariable(inst, extVars)
        elif isinstance(inst, di.Immediate) : return self.CreateVertexImmediate(inst, extVars)
        elif isinstance(inst, di.FunctionCall) : return self.CreateVertexFuncCall(inst, extVars)    
        elif isinstance(inst, di.ArrayCall) : return self.CreateVertexArrayLoad(inst, extVars)
        elif isinstance(inst, di.BinOperation) : return self.CreateVertexBinOp(inst, extVars)
        elif isinstance(inst, di.Statement) :
            if inst.comparator == "<-" : return self.CreateVertexArrayStore(inst, extVars)
            elif inst.comparator == "=" :
                if isinstance(inst.lhs, di.ArrayCall) : return self.CreateVertexArrayStore(inst, extVars)
                else : return self.CreateVertexAssign(inst, extVars)
            else : return self.CreateVertexCompare(inst, extVars)
        elif isinstance(inst, di.Conditional) : return self.CreateVertexCond(inst, extVars)
        elif isinstance(inst, di.UnOperation) : return self.CreateVertexUnOp(inst, extVars)
        elif isinstance(inst, di.DataRegion) : return self.CreateVertexDataRegion(inst, extVars)
        else : sys.exit("%s is not something I had in mind. DepGraph->AddDslInstructionHelper" % (inst))

    def CreateVertexDataRegion(self, data, extVars) :
        dataVertex = VertexNode()
        dataVertex.operands = None
        dataVertex.operator = VertexNode.OpCode.NONE
        dataVertex.value = None
        dataVertex.name = ""
        dataVertex.index = 0
        dataVertex.programOrigin = data.var.programOrigin
        dataVertex.type = VertexNode.VertexType.DATAREGION
        dataVertex.bitlength = 0

        varVertex = self.AddDslInstructionHelper(data.var, extVars)
        lowerVertex = self.AddDslInstructionHelper(data.lower, extVars)
        upperVertex = self.AddDslInstructionHelper(data.upper, extVars)

        dataVertex.operands = [varVertex, lowerVertex, upperVertex]
        self.vertices.append(dataVertex)
        return dataVertex
            
    def CreateVertexVariable(self, var, extVars) :
        # If vertex already exists, return the vertex.
        varVertex = self.FindVertexWithName(var.name, var.ssaIndex, var.programOrigin)
        if varVertex != None: return varVertex

        # Otherwise, it might be in the list of external variables
        varVertex = self.FindVertexWithNameFromList(var.name, var.ssaIndex, var.programOrigin, extVars)
        # If you find it in extVars, use it, but also add it to the current vertices.
        if varVertex != None :
            self.vertices.insert(0, varVertex)
            return varVertex
            
        # Else, create a new VertexNode. 
        varVertex = VertexNode()
        varVertex.operands = None
        varVertex.operator = VertexNode.OpCode.NONE
        varVertex.value = None
        varVertex.name = var.name
        varVertex.index = var.ssaIndex
        varVertex.programOrigin = var.programOrigin
        varVertex.type = VertexNode.VertexType.VAR
        varVertex.bitlength = var.length

        # If vertex does not exist, it must be an input.
        self.vertices.insert(0, varVertex)
        return varVertex

    def CreateVertexImmediate(self, imm, extVars) :
        # We will create a vertex for it, but it won't be added to any list
        immVertex = VertexNode()
        immVertex.operands = None
        immVertex.operator = VertexNode.OpCode.NONE
        immVertex.value = imm.value
        immVertex.name = None
        immVertex.index = None
        immVertex.programOrigin = None
        immVertex.type = VertexNode.VertexType.IMM
        immVertex.bitlength = imm.length
        return immVertex

    def CreateVertexFuncCall(self, func, extVars) :
        # Operands: Function name, args
        # Create vertex node for the function name
        fVertex = VertexNode()
        fVertex.operands = None
        fVertex.operator = VertexNode.OpCode.NONE
        fVertex.value = None
        fVertex.name = func.name
        fVertex.index = None
        fVertex.programOrigin = None
        fVertex.type = VertexNode.VertexType.FUNC
        fcOperands = [fVertex]
        for a in func.args :
            tempOperand = self.AddDslInstructionHelper(a, extVars)
            fcOperands.append(tempOperand)
        fcVertex = VertexNode()
        fcVertex.operands = fcOperands
        # Do not add fcVertex to the function name vertex user. Add fcVertex to the user of other
        # operands.
        for op in fcVertex.operands :
            if op.users == None : op.users = []
            op.users.append(fcVertex)
        fcVertex.operator = VertexNode.OpCode.FUNCCALL
        fcVertex.value = None
        fcVertex.name = self.tempName
        fcVertex.index = self.GetNextNameIndex()
        fcVertex.programOrigin = None
        fcVertex.type = VertexNode.VertexType.TEMP
        if fVertex.name == "merge" :
            # args: multiple bitvectors.
            fcVertex.bitlength = 0
            for op in fcVertex.operands[1:] :
                fcVertex.bitlength = fcVertex.bitlength + op.bitlength
        elif fVertex.name == "split" :
            # args: (1) bitvector to split, (2) lower bound, (3) upper bound
            assert(fcVertex.operands[2].type == VertexNode.VertexType.IMM and \
                   fcVertex.operands[3].type == VertexNode.VertexType.IMM)
            fcVertex.bitlength = fcVertex.operands[3].value - fcVertex.operands[2].value + 1
        elif fVertex.name == "zeroext" :
            # args: (1) bitvector to extend, (2) length to extend
            fcVertex.bitlength = fcVertex.operands[1].bitlength + fcVertex.operands[2].value
        elif fVertex.name == "concat" :
            # args: multiple bitvectors.
            fcVertex.bitlength = 0
            for op in fcVertex.operands[1:] :
                fcVertex.bitlength = fcVertex.bitlength + op.bitlength
        else : sys.exit("Unexpected built-in function name : " + fVertex.name)

        self.vertices.insert(0, fcVertex)
        return fcVertex

    def CreateVertexArrayLoad(self, arrld, extVars) :
        # Get the array vertex
        aVertex = self.FindArrayWithName(arrld.name, arrld.ssaIndex, arrld.programOrigin)
        if aVertex == None :
            aVertex = self.FindVertexWithNameFromList(arrld.name, arrld.ssaIndex, arrld.programOrigin, extVars)
            if aVertex != None :
                self.vertices.insert(0, aVertex)

        if aVertex == None :
            aVertex = VertexNode()
            aVertex.operands = None
            aVertex.operator = VertexNode.OpCode.NONE
            aVertex.value = None
            aVertex.name = arrld.name
            aVertex.index = arrld.ssaIndex
            aVertex.programOrigin = arrld.programOrigin
            aVertex.type = VertexNode.VertexType.ARR
            assert(arrld.length != None)
            aVertex.arrayElBitlength = arrld.length
            
            self.vertices.insert(0, aVertex)

        # Get the index vertex
        tempIndex = self.AddDslInstructionHelper(arrld.index, extVars)
        #Update aVertex's arrayIndexBitlength to fit the size of tempIndex
        aVertex.arrayIndexBitlength = tempIndex.bitlength

        # Create Array load vertex
        acVertex = VertexNode()
        acVertex.operands = [aVertex, tempIndex]
        # Add acVertex to operands's users list
        for op in acVertex.operands :
            if op.users == None : op.users = []
            op.users.append(acVertex)
        acVertex.operator = VertexNode.OpCode.LOAD
        acVertex.value = None
        acVertex.name = self.tempName
        acVertex.programOrigin = None
        acVertex.index = self.GetNextNameIndex()
        acVertex.type = VertexNode.VertexType.TEMP
        assert(aVertex.arrayElBitlength != None)
        acVertex.bitlength = aVertex.arrayElBitlength
        
        self.vertices.insert(0, acVertex)
        return acVertex

    def CreateVertexBinOp(self, binop, extVars) :
        # Get left hand side vertex
        lhsVertex = self.AddDslInstructionHelper(binop.lhs, extVars)
        # Get right hand side vertex
        rhsVertex = self.AddDslInstructionHelper(binop.rhs, extVars)
        assert(lhsVertex.bitlength == rhsVertex.bitlength)
        # Create binary operation vertex
        boVertex = VertexNode()
        boVertex.operands = [lhsVertex, rhsVertex]
        # Add acVertex to operands's users list
        for op in boVertex.operands :
            if op.users == None : op.users = []
            op.users.append(boVertex)
        boVertex.operator = VertexNode.OpCode.GetBinOpCode(binop.operator)
        boVertex.value = None
        boVertex.name = self.tempName
        boVertex.index = self.GetNextNameIndex()
        boVertex.programOrigin = None
        boVertex.type = VertexNode.VertexType.TEMP
        boVertex.bitlength = lhsVertex.bitlength
        
        self.vertices.insert(0, boVertex)
        return boVertex

    def CreateVertexAssign(self, assign, extVars) :
        # Get right hand side vertex
        rhsVertex = self.AddDslInstructionHelper(assign.rhs, extVars)
        # Create assignment vertex
        aVertex = VertexNode()
        aVertex.operands = [rhsVertex]
        # Add aVertex to operands's users list
        if rhsVertex.users == None : rhsVertex.users = []
        rhsVertex.users.append(aVertex)
        aVertex.operator = VertexNode.OpCode.ASSIGN
        aVertex.value = None
        aVertex.name = assign.lhs.name
        aVertex.programOrigin = assign.lhs.programOrigin
        aVertex.index = assign.lhs.ssaIndex
        aVertex.type = VertexNode.VertexType.VAR
        aVertex.bitlength = rhsVertex.bitlength
        
        self.vertices.insert(0, aVertex)
        return aVertex

    def CreateVertexArrayStore(self, arrst, extVars) :
        # Get array vertex to store the value into.
        oaVertex = self.FindArrayWithName(arrst.lhs.name, arrst.lhs.oldSsaIndex, arrst.lhs.programOrigin)

        if oaVertex == None :
            oaVertex = self.FindVertexWithNameFromList(arrst.lhs.name, arrst.lhs.oldSsaIndex, \
                                                       arrst.lhs.programOrigin, extVars)
            if oaVertex != None :
                self.vertices.insert(0, oaVertex)
        
        if oaVertex == None :
            oaVertex = VertexNode()
            oaVertex.operands = None
            oaVertex.operator = VertexNode.OpCode.NONE
            oaVertex.value = None
            oaVertex.name = arrst.lhs.name
            oaVertex.index = arrst.lhs.oldSsaIndex
            oaVertex.programOrigin = arrst.lhs.programOrigin
            oaVertex.type = VertexNode.VertexType.ARR
            oaVertex.arrayElBitlength = arrst.lhs.length
            self.vertices.insert(0, oaVertex)
            
        # Get the index of the array
        arrayIndexVertex = self.AddDslInstructionHelper(arrst.lhs.index, extVars)
        # Update oaVertex's arrayIndexBitlength to fit arrayIndexVertex's size
        oaVertex.arrayIndexBitlength = arrayIndexVertex.bitlength
        
        # Get the value to store
        valueToStoreVertex = self.AddDslInstructionHelper(arrst.rhs, extVars)

        # Create the vertex for the newly created array
        stVertex = VertexNode()
        stVertex.operands = [oaVertex, arrayIndexVertex, valueToStoreVertex]
        # Add stVertex to operands's users list
        for op in stVertex.operands :
            if op.users == None : op.users = []
            op.users.append(stVertex)
        stVertex.operator = VertexNode.OpCode.STORE
        stVertex.value = None
        stVertex.name = arrst.lhs.name
        stVertex.index = arrst.lhs.ssaIndex
        stVertex.programOrigin = arrst.lhs.programOrigin
        stVertex.type = VertexNode.VertexType.ARR
        stVertex.arrayElBitlength = oaVertex.arrayElBitlength
        stVertex.arrayIndexBitlength = oaVertex.arrayIndexBitlength

        self.vertices.insert(0, stVertex)
        return stVertex

    def CreateVertexCompare(self, comp, extVars) :
        # Get the left hand side vertex
        lhsVertex = self.AddDslInstructionHelper(comp.lhs, extVars)
        # Get the right hand side vertex
        rhsVertex = self.AddDslInstructionHelper(comp.rhs, extVars)

        # Create the compare vertex
        cVertex = VertexNode()
        cVertex.operands = [lhsVertex, rhsVertex]
        # Add aVertex to operands's users list
        for op in cVertex.operands :
            if op.users == None : op.users = []
            op.users.append(cVertex)
        cVertex.operator = VertexNode.OpCode.GetCompOpCode(comp.comparator)
        cVertex.value = None
        cVertex.name = self.tempName
        cVertex.index = self.GetNextNameIndex()
        cVertex.programOrigin = None
        cVertex.type = VertexNode.VertexType.TEMP
        cVertex.bitlength = -1 # Compare is a boolean. bitlength does not exist.
        
        self.vertices.insert(0, cVertex)
        return cVertex

    def CreateVertexCond(self, cond, extVars) :
        # Get the conditional statement vertex
        condStmtVertex = self.AddDslInstructionHelper(cond.condStmt, extVars)
        # Get the value for the true path
        truePathVertex = self.AddDslInstructionHelper(cond.truePath, extVars)
        # Get the value for the false path
        falsePathVertex = self.AddDslInstructionHelper(cond.falsePath, extVars)

        assert(truePathVertex.bitlength == falsePathVertex.bitlength)
        # Create conditional assignment vertex
        cVertex = VertexNode()
        cVertex.operands = [condStmtVertex, truePathVertex, falsePathVertex]
        # Add cVertex to operands's users list
        for op in cVertex.operands :
            if op.users == None : op.users = []
            op.users.append(cVertex)
        cVertex.operator = VertexNode.OpCode.CONDITIONAL
        cVertex.value = None
        cVertex.name = self.tempName
        cVertex.index = self.GetNextNameIndex()
        cVertex.programOrigin = None
        cVertex.type = VertexNode.VertexType.TEMP
        cVertex.bitlength = truePathVertex.bitlength

        self.vertices.insert(0, cVertex)
        return cVertex

    def CreateVertexUnOp(self, unop, extVars) :
        # Get the right hand side vertex
        rhsVertex = self.AddDslInstructionHelper(unop.rhs, extVars)

        # Create unary operation vertex
        oVertex = VertexNode()
        oVertex.operands = [rhsVertex]
        # Add oVertex to operands's users list
        if rhsVertex.users == None : rhsVertex.users = []
        
        rhsVertex.users.append(oVertex)
        oVertex.operator = VertexNode.OpCode.GetBinOpCode(unop.operator)
        oVertex.value = None
        oVertex.name = self.tempName
        oVertex.index = self.GetNextNameIndex()
        oVertex.programOrigin = None
        oVertex.type = VertexNode.VertexType.TEMP
        oVertex.bitlength = rhsVertex.bitlength

        self.vertices.insert(0, oVertex)
        return oVertex

    def GetNextNameIndex(self) :
        retValue = self.tempNameCounter
        self.tempNameCounter = self.tempNameCounter + 1
        return retValue

    def FindVertexWithNameFromList(self, n, i, po, lst) :
        for v in lst :
            if v.name == n and v.index == i and v.programOrigin == po : return v
        return None
    
    def FindVertexWithName(self, n, i, po) :
        for v in self.vertices :
            if v.name == n and v.index == i and v.programOrigin == po: return v
        return None

    def FindArrayWithName(self, n, i, po) :
        for a in [v for v in self.vertices if v.type == VertexNode.VertexType.ARR] :
            if a.name == n and a.index == i and a.programOrigin == po: return a
        return None

    # Replace fr vertex with to vertex. This means all the users of fr will use to instead.
    def ReplaceVertex(fr, to) :
        # If replace "fr" node to "to" node,

        # for ever user of "fr", for every operands of user, replace "fr" to "to"
        if fr.users != None :
            for user in fr.users :
                user.operands = [to if op == fr else op for op in user.operands]

            # the append user of "fr" to the list of user of "fr"
            if to.users == None : to.users = fr.users
            else : to.users = to.users + fr.users
        
        # If "fr" is progOutput, then now "to" is progOutput
        if "progOutput" in fr.metadata :
            to.AddMetadata("progOutput", fr.RemoveMetadata("progOutput"))

class VertexNode() :
    class VertexType(Enum) :
        NONE = 1
        VAR = 2
        TEMP = 3
        IMM = 4
        ARR = 5
        FUNC = 6
        DATAREGION = 7

        def IsConstant(t) :
            return t == VertexNode.VertexType.IMM or \
                   t == VertexNode.VertexType.FUNC
        def IsVarOrTemp(t) :
            return t == VertexNode.VertexType.VAR or \
                   t == VertexNode.VertexType.TEMP

    class OpCode(Enum) :
        NONE = 0
        PLUS = 1
        MINUS = 2
        AND = 3
        OR = 4
        XOR = 5
        SHL = 6
        SHR = 7
        ROL = 8
        ROR = 9
        NOT = 10
        FUNCCALL = 11
        STORE = 12
        LOAD = 13
        CONDITIONAL = 14
        ASSIGN = 15
        MUL = 16
        DIV = 17
        EQ = 100
        NE = 101
        LT = 102
        LE = 103
        GT = 104
        GE = 105

        def IsComparison(oc) :
            return oc in [VertexNode.OpCode.EQ, VertexNode.OpCode.NE, VertexNode.OpCode.LT, \
                          VertexNode.OpCode.LE, VertexNode.OpCode.GT, VertexNode.OpCode.GE]

        def IsBinaryOp(oc) :
            return oc in [VertexNode.OpCode.PLUS, VertexNode.OpCode.MINUS, VertexNode.OpCode.AND, \
                          VertexNode.OpCode.OR, VertexNode.OpCode.XOR, VertexNode.OpCode.SHL, \
                          VertexNode.OpCode.SHR, VertexNode.OpCode.ROL, VertexNode.OpCode.ROR, \
                          VertexNode.OpCode.MUL, VertexNode.OpCode.DIV]

        def IsUnaryOp(oc) :
            return oc in [VertexNode.OpCode.NOT]
            

        def GetCompOpCode(s) :
            if s == "==" : return VertexNode.OpCode.EQ
            elif s == "!=" : return VertexNode.OpCode.NE
            elif s == "<" : return VertexNode.OpCode.LT
            elif s == "<=" : return VertexNode.OpCode.LE
            elif s == ">" : return VertexNode.OpCode.GT
            elif s == ">=" : return VertexNode.OpCode.GE


        def GetBinOpCode(s) :
            if s == "+" : return VertexNode.OpCode.PLUS
            elif s == "-" : return VertexNode.OpCode.MINUS
            elif s == "&" : return VertexNode.OpCode.AND
            elif s == "|" : return VertexNode.OpCode.OR
            elif s == "^" : return VertexNode.OpCode.XOR
            elif s == "<<" : return VertexNode.OpCode.SHL
            elif s == ">>" : return VertexNode.OpCode.SHR
            elif s == "<<<" : return VertexNode.OpCode.ROL
            elif s == ">>>" : return VertexNode.OpCode.ROR
            elif s == "!" : return VertexNode.OpCode.NOT
            elif s == "*" : return VertexNode.OpCode.MUL
            elif s == "/" : return VertexNode.OpCode.DIV

    def __init__(self) :
        self.operands = None
        self.users = None
        self.operator = None
        self.value = None
        self.name = None
        self.index = None
        self.programOrigin = None
        self.type = None
        self.bitlength = None
        self.arrayElBitlength = None
        self.arrayIndexBitlength = None
        self.topRank = None
        self.equivClassId = None
        self.metadata = {}
        self.addtlConst = None

    def AddMetadata(self, name, val) :
        self.metadata[name] = val
        return

    def RemoveMetadata(self, name) :
        return self.metadata.pop(name, None)

    # Destroys ties between this vertex and its users/operands
    def CutAllTies(self) :
        # Remove link to its operands
        if self.users != None :
            for v in self.users :
                v.RemoveOperand(self)

        # Remove link to its users
        if self.operands != None :
            for v in self.operands :
                v.RemoveUser(self)

        # Clear out dictionary
        self.metadata.clear()

    def RemoveOperand(self, v) :
        if self.operands == None : return
        for i in range(0, len(self.operands)) :
            if self.operands[i] == None : continue
            if self.operands[i] == v : self.operands[i] == None

    def RemoveUser(self, v) :
        if self.users == None : return
        if v in self.users : self.users.remove(v)
        if self.users == [] : self.users = None

    def ShallowCopy(self) :
        nv = VertexNode()
        nv.operator = self.operator
        nv.value = self.value
        nv.name = self.name
        nv.index = self.index
        nv.programOrigin = self.programOrigin
        nv.type = self.type
        nv.bitlength = self.bitlength
        nv.arrayElBitlength = self.arrayElBitlength
        nv.arrayIndexBitlength = self.arrayIndexBitlength
        nv.topRank = self.topRank
        nv.equivClassId = self.equivClassId
        return nv
        
    # ALWAYS caculates topological ranking. This means, if operands do not have topological ranking,
    # it will recursively call CalculateTopRank on its operands.
    def CalculateTopRank(self, reCalculate = False) :
        if self.topRank != None and not reCalculate:
            return self.topRank
        
        if self.operands == None or self.operands == [] :
            if VertexNode.VertexType.IsConstant(self.type) :
                self.topRank = 0
            else :
                self.topRank = 1
            return self.topRank

        maxOperandTopRank = 0
        for o in self.operands :
            opTopRank =  o.CalculateTopRank(reCalculate)
            maxOperandTopRank = opTopRank if opTopRank > maxOperandTopRank else maxOperandTopRank

        self.topRank = maxOperandTopRank + 1
        return self.topRank

    def __eq__(self, other) :
        if other == None : return False
        if self.type != other.type : return False
        if self.type == VertexNode.VertexType.IMM : return self.value == other.value
        return self.name == other.name and \
               self.index == other.index and \
               self.programOrigin == other.programOrigin
        
    def __str__(self) :
        if self.type == VertexNode.VertexType.IMM : return str(self.value)

        s = ""
        if self.programOrigin != None : s = s + self.programOrigin + "."
        if self.name != None : s = s + self.name
        if self.index != None : s = s + "." + str(self.index)
        return s

    def __hash__(self):
        return hash((self.name, self.index, self.programOrigin, self.value, self.type, self.operator))

    # Returns the name of the vertex in SMT form
    def VertexNameToSmt(self) :
        assert(self.type != VertexNode.VertexType.NONE and \
               self.type != VertexNode.VertexType.FUNC)
        
        if self.type == VertexNode.VertexType.VAR :
            return z3.BitVec(self.__str__(), self.bitlength)
            
        if self.type == VertexNode.VertexType.TEMP :
            # is it a boolean?
            if self.bitlength == -1 :
                return z3.Bool(self.__str__())
            return z3.BitVec(self.__str__(), self.bitlength)
            
        if self.type == VertexNode.VertexType.IMM :
            return z3.BitVecVal(self.value, self.bitlength)
            
        if self.type == VertexNode.VertexType.ARR :
            return z3.Array(self.__str__(), \
                            z3.BitVecSort(self.arrayIndexBitlength), \
                            z3.BitVecSort(self.arrayElBitlength))

    def ComparisonToSmt(self) :
        assert(VertexNode.OpCode.IsComparison(self.operator))
        lhs = self.operands[0].VertexNameToSmt()
        rhs = self.operands[1].VertexNameToSmt()
        if self.operator == VertexNode.OpCode.GT :
            return z3.UGT(lhs, rhs)
        elif self.operator == VertexNode.OpCode.GE :
            return z3.UGE(lhs, rhs)
        elif self.operator == VertexNode.OpCode.LT :
            return z3.ULT(lhs, rhs)
        elif self.operator == VertexNode.OpCode.LE :
            return z3.ULE(lhs, rhs)
        elif self.operator == VertexNode.OpCode.EQ :
            return (lhs == rhs)
        elif self.operator == VertexNode.OpCode.NE :
            return (lhs != rhs)

    def VertexSubGraphToSmt(self) :
        if self.type == VertexNode.VertexType.VAR :
            # Might be an input
            if self.operands == None : return self.VertexNameToSmt()
            return self.operands[0].VertexSubGraphToSmt()

        elif self.type == VertexNode.VertexType.TEMP :
            # Possible Vertex : Function Call, Array Load, Binary Operation, Comparison,  
            #                   Conditional Assignment, Unary Operation
            # function call: name = func_name(arguments)
            # array load: name = array[index]
            # binary operation: name = operand1 op operand2
            # comparison: name = operand1 comp operand2
            # conditional assignment: name = ite(operand1, operand2, operand3)
            # unary operation: name = op operand1

            # It's a function call
            if self.operator == VertexNode.OpCode.FUNCCALL :
                assert(self.operands[0].type == VertexNode.VertexType.FUNC)
                # There are four possible functions that can last until now:
                if self.operands[0].name == "merge" :
                    args = []
                    for op in self.operands[1:] :
                        args.append(op.VertexSubGraphToSmt())
                    return z3.Concat(args)
                elif self.operands[0].name == "split" :
                    toSplit = self.operands[1].VertexSubGraphToSmt()
                    # Extract requires actual numerical value.
                    lowerBound = self.operands[2].value
                    upperBound = self.operands[3].value
                    return z3.Extract(upperBound, lowerBound, toSplit)
                elif self.operands[0].name == "zeroext" :
                    toExtend = self.operands[1].VertexSubGraphToSmt()
                    # ZeroExt requires actual numerical value
                    n = self.operands[2].value
                    return z3.ZeroExt(n, toExtend)
                elif self.operands[0].name == "concat" :
                    args = []
                    for op in self.operands[1:] :
                        args.append(op.VertexSubGraphToSmt())
                    return z3.Concat(args)
                
            # It's an array load
            elif self.operator == VertexNode.OpCode.LOAD :
                array = self.operands[0].VertexSubGraphToSmt()
                arrayIndex = self.operands[1].VertexSubGraphToSmt()
                return z3.Select(array, arrayIndex)
                
            # It's a conditional statement
            elif self.operator == VertexNode.OpCode.CONDITIONAL :
                cond = self.operands[0].VertexSubGraphToSmt()
                truePath = self.operands[1].VertexSubGraphToSmt()
                falsePath = self.operands[2].VertexSubGraphToSmt()
                return z3.If(cond, truePath, falsePath)

            # It's a comparison (x < y)
            elif VertexNode.OpCode.IsComparison(self.operator) :
                lhs = self.operands[0].VertexSubGraphToSmt()
                rhs = self.operands[1].VertexSubGraphToSmt()
                if self.operator == VertexNode.OpCode.GT :
                    return z3.UGT(lhs, rhs)
                elif self.operator == VertexNode.OpCode.GE :
                    return z3.UGE(lhs, rhs)
                elif self.operator == VertexNode.OpCode.LT :
                    return z3.ULT(lhs, rhs)
                elif self.operator == VertexNode.OpCode.LE :
                    return z3.ULE(lhs, rhs)
                elif self.operator == VertexNode.OpCode.EQ :
                    return (lhs == rhs)
                elif self.operator == VertexNode.OpCode.NE :
                    return (lhs != rhs)

            # It's a binary operation
            elif VertexNode.OpCode.IsBinaryOp(self.operator) :
                lhs = self.operands[0].VertexSubGraphToSmt()
                rhs = self.operands[1].VertexSubGraphToSmt()
                if self.operator == VertexNode.OpCode.PLUS :                    
                    return (lhs + rhs)
                elif self.operator == VertexNode.OpCode.MINUS :
                    return (lhs - rhs)
                elif self.operator == VertexNode.OpCode.AND :
                    return (lhs & rhs)
                elif self.operator == VertexNode.OpCode.OR :
                    return (lhs | rhs)
                elif self.operator == VertexNode.OpCode.XOR :
                    return (lhs ^ rhs)
                elif self.operator == VertexNode.OpCode.SHL :
                    return (lhs << rhs)
                elif self.operator == VertexNode.OpCode.SHR :
                    return (z3.LShR(lhs, rhs))
                elif self.operator == VertexNode.OpCode.ROL :
                    return (z3.RotateLeft(lhs, rhs))
                elif self.operator == VertexNode.OpCode.ROR :
                    return (z3.RotateRight(lhs, rhs))
                elif self.operator == VertexNode.OpCode.MUL :
                    return (lhs * rhs)
                elif self.operator == VertexNnode.OpCode.DIV :
                    return (lhs / rhs)
                
            # It's a unary operation
            elif VertexNode.OpCode.IsUnaryOp(self.operator) :
                rhs = self.operands[0].VertexSubGraphToSmt()
                if self.operator == VertexNode.OpCode.NOT :
                    return ~rhs

            
        elif self.type == VertexNode.VertexType.IMM :
            # Possible Vertex : Immediate Value
            return self.VertexNameToSmt()
        elif self.type == VertexNode.VertexType.ARR :
            # Possible Vertex : Input array, array store
            # input array: there is nothing to do
            # array store: newarray = store(array, index, value)

            # if operator == None, it's an "input" array
            if self.operator == None : return self.VertexNameToSmt()
            if self.operator == VertexNode.OpCode.NONE : return self.VertexNameToSmt()
            # Otherwise, it must be an array store operation vertex
            assert(self.operator == VertexNode.OpCode.STORE)
            oldArray = self.operands[0].VertexSubGraphToSmt()
            index = self.operands[1].VertexSubGraphToSmt()
            value = self.operands[2].VertexSubGraphToSmt()
            return z3.Store(oldArray, index, value)
            
        elif self.type == VertexNode.VertexType.FUNC :
            # Possible Vertex : Name of the function
            return self.VertexNameToSmt()

    # returns the instruction of the vertex in SMT formula.
    def VertexOperationToSmt(self) :
        assert(self.type != VertexNode.VertexType.NONE)
        
        if self.type == VertexNode.VertexType.VAR :
            # Possible Vertex : input Variable, name = operand1
            # input variable: there is nothing to do.
            # assigned Variable: name = operands[0]

            # It's an input variable if there is no operand :
            if self.operands == None : return None
            # otherwise, it's an assigned variable, but make sure just in case
            assert(self.operator == VertexNode.OpCode.ASSIGN)
            return self.VertexNameToSmt() == self.operands[0].VertexNameToSmt()
            
        elif self.type == VertexNode.VertexType.TEMP :
            # Possible Vertex : Function Call, Array Load, Binary Operation, Comparison,  
            #                   Conditional Assignment, Unary Operation
            # function call: name = func_name(arguments)
            # array load: name = array[index]
            # binary operation: name = operand1 op operand2
            # comparison: name = operand1 comp operand2
            # conditional assignment: name = ite(operand1, operand2, operand3)
            # unary operation: name = op operand1

            # It's a function call
            if self.operator == VertexNode.OpCode.FUNCCALL :
                assert(self.operands[0].type == VertexNode.VertexType.FUNC)
                # There are four possible functions that can last until now:
                if self.operands[0].name == "merge" :
                    args = []
                    for op in self.operands[1:] :
                        args.append(op.VertexNameToSmt())
                    return self.VertexNameToSmt() == z3.Concat(args)
                elif self.operands[0].name == "split" :
                    toSplit = self.operands[1].VertexNameToSmt()
                    # Extract requires actual numerical value.
                    lowerBound = self.operands[2].value
                    upperBound = self.operands[3].value
                    return self.VertexNameToSmt() == z3.Extract(upperBound, lowerBound, toSplit)
                elif self.operands[0].name == "zeroext" :
                    toExtend = self.operands[1].VertexNameToSmt()
                    # ZeroExt requires actual numerical value
                    n = self.operands[2].value
                    return self.VertexNameToSmt() == z3.ZeroExt(n, toExtend)
                elif self.operands[0].name == "concat" :
                    args = []
                    for op in self.operands[1:] :
                        args.append(op.VertexNameToSmt())
                    return self.VertexNameToSmt() == z3.Concat(args)
                
            # It's an array load
            elif self.operator == VertexNode.OpCode.LOAD :
                array = self.operands[0].VertexNameToSmt()
                arrayIndex = self.operands[1].VertexNameToSmt()
                return self.VertexNameToSmt() == z3.Select(array, arrayIndex)
                
            # It's a conditional statement
            elif self.operator == VertexNode.OpCode.CONDITIONAL :
                cond = self.operands[0].VertexNameToSmt()
                truePath = self.operands[1].VertexNameToSmt()
                falsePath = self.operands[2].VertexNameToSmt()
                return self.VertexNameToSmt() == z3.If(cond, truePath, falsePath)

            # It's a comparison (x < y)
            elif VertexNode.OpCode.IsComparison(self.operator) :
                lhs = self.operands[0].VertexNameToSmt()
                rhs = self.operands[1].VertexNameToSmt()
                if self.operator == VertexNode.OpCode.GT :
                    return self.VertexNameToSmt() == z3.UGT(lhs, rhs)
                elif self.operator == VertexNode.OpCode.GE :
                    return self.VertexNameToSmt() == z3.UGE(lhs, rhs)
                elif self.operator == VertexNode.OpCode.LT :
                    return self.VertexNameToSmt() == z3.ULT(lhs, rhs)
                elif self.operator == VertexNode.OpCode.LE :
                    return self.VertexNameToSmt() == z3.ULE(lhs, rhs)
                elif self.operator == VertexNode.OpCode.EQ :
                    return self.VertexNameToSmt() == (lhs == rhs)
                elif self.operator == VertexNode.OpCode.NE :
                    return self.VertexNameToSmt() == (lhs != rhs)

            # It's a binary operation
            elif VertexNode.OpCode.IsBinaryOp(self.operator) :
                lhs = self.operands[0].VertexNameToSmt()
                rhs = self.operands[1].VertexNameToSmt()
                if self.operator == VertexNode.OpCode.PLUS :                    
                    return self.VertexNameToSmt() == (lhs + rhs)
                elif self.operator == VertexNode.OpCode.MINUS :
                    return self.VertexNameToSmt() == (lhs - rhs)
                elif self.operator == VertexNode.OpCode.AND :
                    return self.VertexNameToSmt() == (lhs & rhs)
                elif self.operator == VertexNode.OpCode.OR :
                    return self.VertexNameToSmt() == (lhs | rhs)
                elif self.operator == VertexNode.OpCode.XOR :
                    return self.VertexNameToSmt() == (lhs ^ rhs)
                elif self.operator == VertexNode.OpCode.SHL :
                    return self.VertexNameToSmt() == (lhs << rhs)
                elif self.operator == VertexNode.OpCode.SHR :
                    return self.VertexNameToSmt() == (z3.LShR(lhs, rhs))
                elif self.operator == VertexNode.OpCode.ROL :
                    return self.VertexNameToSmt() == (z3.RotateLeft(lhs, rhs))
                elif self.operator == VertexNode.OpCode.ROR :
                    return self.VertexNameToSmt() == (z3.RotateRight(lhs, rhs))
                elif self.operator == VertexNode.OpCode.MUL :
                    return self.VertexNameToSmt() == (lhs * rhs)
                elif self.operator == VertexNnode.OpCode.DIV :
                    return self.VertexNameToSmt() == (lhs / rhs)
                
            # It's a unary operation
            elif VertexNode.OpCode.IsUnaryOp(self.operator) :
                rhs = self.operands[0].VertexNameToSmt()
                if self.operator == VertexNode.OpCode.NOT :
                    return self.VertexNameToSmt() == ~rhs

            
        elif self.type == VertexNode.VertexType.IMM :
            # Possible Vertex : Immediate Value
            return None
        elif self.type == VertexNode.VertexType.ARR :
            # Possible Vertex : Input array, array store
            # input array: there is nothing to do
            # array store: newarray = store(array, index, value)

            # if operator == None, it's an "input" array
            if self.operator == None : return None
            if self.operator == VertexNode.OpCode.NONE : return None
            # Otherwise, it must be an array store operation vertex
            assert(self.operator == VertexNode.OpCode.STORE)
            oldArray = self.operands[0].VertexNameToSmt()
            index = self.operands[1].VertexNameToSmt()
            value = self.operands[2].VertexNameToSmt()
            newArray = self.VertexNameToSmt()
            return newArray == z3.Store(oldArray, index, value)
            
        elif self.type == VertexNode.VertexType.FUNC :
            # Possible Vertex : Name of the function
            return None
        

