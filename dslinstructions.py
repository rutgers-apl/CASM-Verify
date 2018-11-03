import z3
import config

class Value :
    def __init(self) :
        pass

    def FindAndReplace(self, fr, to) :
        return

    def ReplaceFunction(self, functions) :
        return
    
    def UpdateSsaIndex(self, IndexMapping, update = False) :
        return

class Variable(Value) :
    def __init__(self, s = None) :
        self.name = ""
        self.ssaIndex = 0
        self.length = 32 # 32 is the default value.
        self.programOrigin = None
        if s != None :
            self.name = s

    def SetProgramOrigin(self, po, override) :
        if self.programOrigin != None and not override : return
        self.programOrigin = po

    def InlineArrayReadWrite(self, arrToInlineList) :
        return None

    def AnalyzeArrayIndexOnlyConst(self, l) :
        return

    def ConstantPropagate(self) :
        return None

    def Copy(self) :
        newStmt = Variable()
        newStmt.name = self.name
        newStmt.length = self.length
        newStmt.ssaIndex = self.ssaIndex
        newStmt.programOrigin = self.programOrigin
        return newStmt

    def Equals(self, to, everything = False) :
        if self.name != to.name :
            return False
        if self.programOrigin != to.programOrigin :
            return False
        if everything and (self.ssaIndex != to.ssaIndex) :
            return False
        return True

    def FindAndReplace(self, fr, to) :
        if self.Equals(fr) :
            return to
        else :
            return None

    def GetSsaName(self) :
        if self.programOrigin == None : return self.name + "." + str(self.ssaIndex)
        return self.programOrigin + "." + self.name + "." + str(self.ssaIndex)

    def ToString(self) :
        if self.length != 32 :
            return self.GetSsaName() + ":" + str(self.length)
        return self.GetSsaName()

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        if not (self.name, self.programOrigin) in IndexMapping :
            IndexMapping[(self.name, self.programOrigin)] = 0
        if update :
            IndexMapping[(self.name, self.programOrigin)] = IndexMapping[(self.name, self.programOrigin)] + 1
        self.ssaIndex = IndexMapping[(self.name, self.programOrigin)]
        
class Immediate(Value) :
    def __init__(self, s = None) :
        self.value = 0
        self.length = 32
        if s != None :
            self.value = int(s, 0)

    def SetProgramOrigin(self, po, override) :
        return
    
    def __eq__(self, imm) :
        if imm == None :
            return False
        return self.value == imm.value

    def __lt__(self, imm) :
        return self.value < imm.value

    def __gt__(self, imm) :
        return self.value > imm.value

    def __add__(self, other) :
        if isinstance(other, int) :
            retImm = Immediate()
            retImm.length = self.length
            retImm.value = self.value + other
            return retImm
        elif isinstance(other, Immediate) :
            retImm = Immediate()
            retImm.length = self.length
            retImm.value = self.value + other.value
            return retImm
        else :
            return NotImplemented

    def InlineArrayReadWrite(self, arrToInlineList) :
        return None

    def AnalyzeArrayIndexOnlyConst(self, l) :
        return

    def ConstantPropagate(self) :
        return None
        
    def Copy(self) :
        newImm = Immediate()
        newImm.value = self.value
        newImm.length = self.length
        return newImm

    def Equals(self, to, everything = False) :
        if self.value != to.value :
            return False
        return True

    def ToString(self) :
        if self.length != 32 :
            return str(self.value) + ":" + str(self.length)
        return str(self.value)

class DataRegion(Value) :
    def __init__(self, inVar, inLower, inUpper) :
        self.var = inVar
        self.lower = inLower
        self.upper = inUpper

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.var.UpdateSsaIndex(IndexMapping)
        self.lower.UpdateSsaIndex(IndexMapping)
        self.upper.UpdateSsaIndex(IndexMapping)

    def ToString(self) :
        varString = self.var.ToString()
        lowerString = self.lower.ToString()
        upperString = self.upper.ToString()
        return "@Data{" + varString + ", " + lowerString + " ~ " + upperString + "};"

    def ConstantPropagate(self) :
        tempVal = self.var.ConstantPropagate()
        if tempVal != None : self.var = tempVal
        tempVal = self.lower.ConstantPropagate()
        if tempVal != None : self.lower = tempVal
        tempVal = self.upper.ConstantPropagate()
        if tempVal != None : self.upper = tempVal
        return None

class FunctionCall(Value) :
    def __init__(self, inName, inArgs) :
        self.name = inName
        self.args = inArgs
        self.programOrigin = None
        self.length = 32

    def SetProgramOrigin(self, po, override) :
        for a in self.args :
            a.SetProgramOrigin(po, override)

        if self.programOrigin != None and not override : return
        self.programOrigin = po


    def InlineArrayReadWrite(self, arrToInlineList) :
        for i in range(0, len(self.args)) :
            tempArg = self.args[i].InlineArrayReadWrite(arrToInlineList)
            if tempArg != None : self.args[i] = tempArg
        return None

    def AnalyzeArrayIndexOnlyConst(self, l) :
        for a in self.args :
            a.AnalyzeArrayIndexOnlyConst(l)
        return

    def ConstantPropagate(self) :
        for i in range(0, len(self.args)) :
            tempArg = self.args[i].ConstantPropagate()
            if tempArg != None : self.args[i] = tempArg
        return None

    def Copy(self) :
        newArgs = []
        for a in self.args :
            newArgs.append(a.Copy())
        newFC = FunctionCall(self.name, newArgs)
        newFC.programOrigin = self.programOrigin
        newFC.length = self.length
        return newFC

    def FindAndReplace(self, fr, to) :
        for i in range(0, len(self.args)) :
            newA = self.args[i].FindAndReplace(fr, to)
            if newA != None :
                self.args[i] = newA

    def ReplaceFunction(self, functions) :
        if self.name in functions :
            fm = functions[self.name]
            if isinstance(fm, Macro) :
                insts = []
                for s in fm.stmts :
                    insts.append(s.Copy())
                for p, a in zip(fm.param, self.args) :
                    for i in insts :
                        i.FindAndReplace(p, a)
                return insts
            elif isinstance(fm, Function) :
                expr = fm.stmt.expr
                for p, a in zip(fm.args, self.args) :
                    expr.FindAndReplace(p, a)
                return expr

    def ToString(self) :
        argString = ""
        for a in self.args :
            if not argString == "" :
                argString = argString + ", "
            argString = argString + a.ToString()
        if self.programOrigin == None : return self.name + "(" + argString + ")"
        return self.programOrigin + "." + self.name + "(" + argString + ")"

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        for a in self.args :
            a.UpdateSsaIndex(IndexMapping)


class ArrayCall(Value) :
    def __init__(self, name = None, inIndex = None) :
        self.name = ""
        if not name == None :
            self.name = name
        self.ssaIndex = 0
        self.index = inIndex
        self.programOrigin = None
        self.oldSsaIndex = None
        self.length = 32

    def SetProgramOrigin(self, po, override) :
        self.index.SetProgramOrigin(po, override)
        
        if self.programOrigin != None and not override : return
        self.programOrigin = po

    def InlineArrayReadWrite(self, arrToInlineList) :
        if self.name in arrToInlineList :
            retVar = Variable()
            retVar.name = "__" + self.name + "_" + str(self.index.value)
            retVar.length = self.length
            retVar.programOrigin = self.programOrigin
            return retVar

    def AnalyzeArrayIndexOnlyConst(self, d) :
        if not self.name in d : d[self.name] = True
        if not isinstance(self.index, Immediate) : d[self.name] = False
        return

    def ConstantPropagate(self) :
        tempIndex = self.index.ConstantPropagate()
        if tempIndex != None : self.index = tempIndex
        return None
        
    def Copy(self) :
        newStmt = ArrayCall()
        newStmt.name = self.name
        newStmt.index = self.index.Copy()
        newStmt.length = self.length
        newStmt.programOrigin = self.programOrigin
        return newStmt

    def FindAndReplace(self, p, a) :
        newIndex = self.index.FindAndReplace(p, a)
        if newIndex != None :
            self.index = newIndex
        return

    def ToString(self) :
        retString = ""
        if self.programOrigin != None : retString = retString + self.programOrigin + "."
            
        retString = retString + self.name + "." + str(self.ssaIndex) + ":" + str(self.length) + "[" + self.index.ToString() + "]"
        
        if not self.oldSsaIndex == None :
            retString = retString + " (old: " + self.programOrigin + "." + self.name + "." + str(self.oldSsaIndex) + ":" + str(self.length) + ")"
        return retString

    def GetSsaName(self) :
        return self.programOrigin + "." + self.name + "." + str(self.ssaIndex)

    def GetOldSsaName(self) :
        if self.oldSsaIndex == None :
            sys.exit("Array Call does not have old ssa name.")
        return self.programOrigin + "." + self.name + "." + str(self.oldSsaIndex)

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        if update :
            if not (self.name, self.programOrigin) in IndexMapping :
                IndexMapping[(self.name, self.programOrigin)] = 0
            self.oldSsaIndex = IndexMapping[(self.name, self.programOrigin)]
            IndexMapping[(self.name, self.programOrigin)] = IndexMapping[(self.name, self.programOrigin)] + 1
            self.ssaIndex = IndexMapping[(self.name, self.programOrigin)]
        else :
            if not (self.name, self.programOrigin) in IndexMapping :
                IndexMapping[(self.name, self.programOrigin)] = 0
            self.ssaIndex = IndexMapping[(self.name, self.programOrigin)]
        self.index.UpdateSsaIndex(IndexMapping)

    def ReplaceFunction(self, functions) :
        newIndex = self.index.ReplaceFunction(functions)
        if newIndex != None :
            self.index = newIndex
        return

class BinOperation(Value) :
    def __init__(self, lhs = None, op = None, rhs = None) :
        self.operator = ""
        self.length = 32
        self.lhs = None
        self.rhs = None
        self.programOrigin = None
        if not op is None :
            self.operator = op
            self.lhs = lhs
            self.rhs = rhs

    def SetProgramOrigin(self, po, override) :
        self.lhs.SetProgramOrigin(po, override)
        self.rhs.SetProgramOrigin(po, override)
        
        if self.programOrigin != None and not override : return
        self.programOrigin = po


    def InlineArrayReadWrite(self, arrToInlineList) :
        tempLhs = self.lhs.InlineArrayReadWrite(arrToInlineList)
        if tempLhs != None : self.lhs = tempLhs
        tempRhs = self.rhs.InlineArrayReadWrite(arrToInlineList)
        if tempRhs != None : self.rhs = tempRhs
        return None

    def AnalyzeArrayIndexOnlyConst(self, d) :
        self.lhs.AnalyzeArrayIndexOnlyConst(d)
        self.rhs.AnalyzeArrayIndexOnlyConst(d)
        return
            
    def ConstantPropagate(self) :
        tempLhs = self.lhs.ConstantPropagate()
        if tempLhs != None : self.lhs = tempLhs
        tempRhs = self.rhs.ConstantPropagate()
        if tempRhs != None : self.rhs = tempRhs

        if isinstance(self.lhs, Immediate) and isinstance(self.rhs, Immediate) :
            # Then we can add the number, and return a new Immediate object
            if self.operator == "+" :
                assert(self.lhs.length == self.rhs.length)
                retImmObj = Immediate()
                retImmObj.value = self.lhs.value + self.rhs.value
                retImmObj.length = self.lhs.length
                return retImmObj
            elif self.operator == "-" :
                assert(self.lhs.length == self.rhs.length)
                retImmObj = Immediate()
                retImmObj.value = self.lhs.value - self.rhs.value
                retImmObj.length = self.lhs.length
                return retImmObj

        if self.operator == "+" :
            if isinstance(self.lhs, Immediate) and self.lhs.value == 0 :
                return self.rhs
            elif isinstance(self.rhs, Immediate) and self.rhs.value == 0 :
                return self.lhs



        if self.operator == "-" :
            if isinstance(self.lhs, Immediate) and self.lhs.value == 0 :
                return self.rhs
            elif isinstance(self.rhs, Immediate) and self.rhs.value == 0 :
                return self.lhs

        return None

    def Copy(self) :
        newStmt = BinOperation()
        newStmt.operator = self.operator
        newStmt.lhs = self.lhs.Copy()
        newStmt.rhs = self.rhs.Copy()
        newStmt.programOrigin = self.programOrigin
        return newStmt

    def FindAndReplace(self, fr, to) :
        newLhs = self.lhs.FindAndReplace(fr, to)
        if newLhs != None :
            self.lhs = newLhs
        newRhs = self.rhs.FindAndReplace(fr, to)
        if newRhs != None :
            self.rhs = newRhs

    def ReplaceFunction(self, functions) :
        newLhs = self.lhs.ReplaceFunction(functions)
        if newLhs != None :
            self.lhs = newLhs
        newRhs = self.rhs.ReplaceFunction(functions)
        if newRhs != None :
            self.rhs = newRhs
        return

    def ToString(self) :
        return "(" + self.lhs.ToString() + " " + self.operator + " " + self.rhs.ToString() + ")"

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.lhs.UpdateSsaIndex(IndexMapping, update)
        self.rhs.UpdateSsaIndex(IndexMapping, update)

        
class UnOperation(Value) :
    def __init__(self, op = None, rhs = None) :
        self.operator = ""
        self.length = 32
        self.rhs = None
        self.programOrigin = None
        if not op is None :
            self.operator = op
            self.rhs = rhs

    def SetProgramOrigin(self, po, override) :
        self.rhs.SetProgramOrigin(po, override)
        if self.programOrigin != None and not override : return
        self.programOrigin = po

    def InlineArrayReadWrite(self, arrToInlineList) :
        tempRhs = self.rhs.InlineArrayReadWrite(arrToInlineList)
        if tempRhs != None : self.rhs = tempRhs
        return None

    def AnalyzeArrayIndexOnlyConst(self, d) :
        self.rhs.AnalyzeArrayIndexOnlyConst(d)
        return

    def ConstantPropagate(self) :
        tempRhs = self.rhs.ConstantPropagate()
        if tempRhs != None : self.rhs = tempRhs
        return None

    def Copy(self) :
        newStmt = UnOperation()
        newStmt.operator = self.operator
        newStmt.rhs = self.rhs.Copy()
        newStmt.programOrigin = self.programOrigin
        return newStmt

    def FindAndReplace(self, fr, to) :
        newRhs = self.rhs.FindAndReplace(fr, to)
        if newRhs != None :
            self.rhs = newRhs

    def ReplaceFunction(self, functions) :
        newRhs = self.rhs.ReplaceFunction(functions)
        if newRhs != None :
            self.rhs = newRhs
        return

    def ToString(self) :
        return self.operator + " " + self.rhs.ToString()

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.rhs.UpdateSsaIndex(IndexMapping, update)

class Statement(Value):
    def __init__(self, lhs = None, comparator = None, rhs = None) :
        self.length = 32
        self.disabled = False
        self.lhs = None
        self.comparator = ""
        self.rhs = None
        self.programOrigin = None
        if comparator != None :
            self.lhs = lhs
            self.rhs = rhs
            if isinstance(self.lhs, ArrayCall) and comparator == "=" :
                self.comparator = "<-"
            else :
                self.comparator = comparator

    def SetProgramOrigin(self, po, override) :
        self.lhs.SetProgramOrigin(po, override)
        self.rhs.SetProgramOrigin(po, override)
        
        if self.programOrigin != None and not override : return
        self.programOrigin = po

    def InlineArrayReadWrite(self, arrToInlineList) :
        tempLhs = self.lhs.InlineArrayReadWrite(arrToInlineList)
        if tempLhs != None :
            self.lhs = tempLhs
            if self.comparator == "<-" : self.comparator = "="
        tempRhs = self.rhs.InlineArrayReadWrite(arrToInlineList)
        if tempRhs != None : self.rhs = tempRhs
        return None


    def AnalyzeArrayIndexOnlyConst(self, d) :
        self.lhs.AnalyzeArrayIndexOnlyConst(d)
        self.rhs.AnalyzeArrayIndexOnlyConst(d)
        return

    def ConstantPropagate(self) :
        tempLhs = self.lhs.ConstantPropagate()
        if tempLhs != None : self.lhs = tempLhs
        tempRhs = self.rhs.ConstantPropagate()
        if tempRhs != None : self.rhs = tempRhs
        return None

    def Copy(self) :
        newStmt = Statement()
        newStmt.lhs = self.lhs.Copy()
        newStmt.comparator = self.comparator
        newStmt.rhs = self.rhs.Copy()
        newStmt.programOrigin = self.programOrigin
        return newStmt
        
    def FindAndReplace(self, fr, to) :
        newLhs = self.lhs.FindAndReplace(fr, to)
        if newLhs != None :
            self.lhs = newLhs
        newRhs = self.rhs.FindAndReplace(fr, to)
        if newRhs != None :
            self.rhs = newRhs

    def ReplaceFunction(self, functions) :
        newLhs = self.lhs.ReplaceFunction(functions)
        if newLhs != None :
            self.lhs = newLhs
        newRhs = self.rhs.ReplaceFunction(functions)
        if newRhs != None :
            self.rhs = newRhs

    def ToString(self) :
        return self.lhs.ToString() + " " + self.comparator + " " + self.rhs.ToString()

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.rhs.UpdateSsaIndex(IndexMapping)
        if self.comparator in ["=", "<-"] :
            self.lhs.UpdateSsaIndex(IndexMapping, True)
        else :
            self.lhs.UpdateSsaIndex(IndexMapping, False)

class Conditional(Value) :
    def __init__(self, cs, tp, fp) :
        self.condStmt = cs
        self.truePath = tp
        self.falsePath = fp
        self.programOrigin = None

    def SetProgramOrigin(self, po, override) :
        self.condStmt.SetProgramOrigin(po, override)
        self.truePath.SetProgramOrigin(po, override)
        self.falsePath.SetProgramOrigin(po, override)
        
        if self.programOrigin != None and not override : return
        self.programOrigin = po

    def InlineArrayReadWrite(self, arrToInlineList) :
        tempStmt = self.condStmt.InlineArrayReadWrite(arrToInlineList)
        if tempStmt != None : self.condStmt = tempStmt

        tempStmt = self.truePath.InlineArrayReadWrite(arrToInlineList)
        if tempStmt != None : self.truePath = tempStmt

        tempStmt = self.falsePath.InlineArrayReadWrite(arrToInlineList)
        if tempStmt != None : self.falsePath = tempStmt

        return None

    def AnalyzeArrayIndexOnlyConst(self, d) :
        self.condStmt.AnalyzeArrayIndexOnlyConst(d)
        return

    def ConstantPropagate(self) :
        tempCond = self.condStmt.ConstantPropagate()
        if tempCond != None : self.condStmt = tempCond
        return None

    def Copy(self) :
        cs = self.condStmt.Copy()
        tp = self.truePath.Copy()
        fp = self.falsePath.Copy()
        newCndtnl = Conditional(cs, tp, fp)
        newCndtnl.programOrigin = self.programOrigin
        return newCndtnl

    def FindAndReplace(self, fr, to) :
        newCondStmt = self.condStmt.FindAndReplace(fr, to)
        if newCondStmt != None :
            self.condStmt = newCondStmt

    def ReplaceVariable(self, iName, iVal) :
        self.condStmt.ReplaceVariable(iName, iVal)
        self.truePath.ReplaceVariable(iName, iVal)
        self.falsePath.ReplaceVariable(iName, iVal)

    def ToString(self) :
        return "(" + self.condStmt.ToString() + ") ? " + self.truePath.ToString() + " : " + self.falsePath.ToString()
    
    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.condStmt.UpdateSsaIndex(IndexMapping, False)
        self.truePath.UpdateSsaIndex(IndexMapping, False)
        self.falsePath.UpdateSsaIndex(IndexMapping, False)

class Macro(Value):
    def __init__(self, name, param, stmts) :
        self.disabled = False
        self.name = name
        self.param = param
        self.stmts = stmts
        self.programOrigin = None

    def ToString(self) :
        paramString = ""
        for p in self.param :
            if not paramString == "" :
                paramString = paramString + ", "
            paramString = paramString + p.ToString()

        stmtString = ""
        for s in self.stmts :
            if not stmtString == "" :
                stmtString = stmtString + "\n"
            stmtString = stmtString + "  " + s.ToString()

        if self.programOrigin == None : return "macro " + self.name + "(" + paramString + ") {\n" + stmtString + "\n}"
        
        return "macro " + self.programOrigin + "." + self.name + "(" + paramString + ") {\n" + stmtString + "\n}"

class Function(Value):
    def __init__(self, name, args, stmt) :
        self.disabled = False
        self.ssaIndex = 0
        self.name = name
        self.args = args
        self.stmt = stmt
        self.programOrigin = None
        
    def ToString(self) :
        argString = ""
        for a in self.args :
            if not argString == "" :
                argString = argString + ", "
            argString = argString + a.ToString()

        if self.programOrigin == None :
            return "def " + self.name + "(" + argString + ") {\n" + self.stmt.ToString() + "}"
        
        return "def " + self.programOrigin + "." + self.name + "(" + argString + ") {\n" + self.stmt.ToString() + "}"

class Loop(Value):
    def __init__(self, index, lbound, ubound, expr) :
        self.disabled = False
        self.i = index
        self.lb = lbound
        self.ub = ubound
        self.expr = expr
        self.programOrigin = None

    def ReplaceFunction(self, functions) :
        i = 0
        while i < len(self.expr) :
            da = self.expr[i]
            retVal = da.ReplaceFunction(functions)
            if retVal != None :
                self.expr[i:i+1] = retVal
                i = i - 1
            i = i + 1

    def ToString(self) :
        retString = "for (" + self.i.ToString() + " = " + str(self.lb.ToString()) + " to " + str(self.ub.ToString()) + ") {\n"
        for e in self.expr :
            retString = retString + "\t" + e.ToString() + "\n"
        return retString + "}"

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        # Technically this should never be called... but just in case.
        for e in self.expr :
            e.UpdateSsaIndex(IndexMapping, update)

class ReturnStatement(Value):
    def __init__(self, expr) :
        self.disabled = False
        self.expr = None
        if expr != None :
            self.expr = expr

    def ToString(self) :
        return "return " + self.expr.ToString()

    def UpdateSsaIndex(self, IndexMapping, update = False) :
        self.expr.UpdateSsaIndex(IndexMapping)
