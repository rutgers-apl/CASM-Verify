import pyparse.pyparsing as pp
import dslinstructions as di
import config

def isImmediate(val) :
    try:
        val = int(val, 0)
        return True
    except ValueError:
        return False

# The idea is to "recursively" put units into a list. So an instruction will contain a list which might contain a list that constains a list, etc...
# So the easiest thing is, put each unit in a list
# Expressions that contain operations are a bit trickier I suppose. Will have to use 2 stacks to make it look like a functional program

def CreateVar(s, loc, toks) :
    t = toks[0]
    toklen = len(toks)

    progOrig = None
    varVal = None
    bitlength = None

    # if length is 1, then only varVal exists
    if len(toks) == 1 :
        varVal = toks[0]
    # if length is 2, then either we have progOrig + varVal, or varVal + bitlength
    elif len(toks) == 2 :
        if toks[0].endswith(".") :
            progOrig = toks[0][:-1]
            varVal = toks[1]
        else :
            varVal = toks[0]
            bitlength = toks[1][1:]
    # if length is 3, then we have progOrig + varVal + bitlength
    elif len(toks) == 3 :
        progOrig = toks[0][:-1]
        varVal = toks[1]
        bitlength = toks[2][1:]

    # Check if it's a label
    if varVal.startswith("L$") :
        temp = di.Label(varVal)
        return [temp]
    # Check if it's a decimal value
    elif isImmediate(varVal) :
        temp = di.Immediate(varVal)
        if bitlength != None :
            temp.length = int(bitlength)
        return [temp]
    # Check if it's a hex value
    elif varVal.startswith("0x") :
        temp = di.Immediate(varVal)
        if bitlength != None :
            temp.length = int(bitlength)
        return [temp]
    # Check if it's a register
    elif varVal.startswith("%") :
        temp = di.Variable(varVal)
        if bitlength != None :
            temp.length = int(bitlength)
        if progOrig != None :
            temp.programOrigin = progOrig
        return [temp]
    # Otherwise it's a variable
    else :
        temp = di.Variable(varVal)
        if bitlength != None :
            temp.length = int(bitlength)
        if progOrig != None :
            temp.programOrigin = progOrig
        return [temp]

def parseMacro(s, loc, toks) :
    temp = di.Macro(toks[0], toks[2], toks[3:])
    return temp

def parseLoop(s, loc, toks) :
    temp = di.Loop(toks[0], toks[1], toks[2], toks[3:])
    return temp

def parseIfExpression(s, loc, toks) :
    if len(toks) == 1 :
        return toks

    tempStmt = di.Statement(toks[0], toks[1], toks[2])
    temp = di.Conditional(tempStmt, toks[4], toks[6])
    return temp

def pushJumpStmt(s, loc, toks) :
    temp = di.JmpStatement(toks[1])
    return temp

def pushExprStmt(s, loc, toks) :
    temp = di.Statement(toks[0], toks[1], toks[2])
    return [temp]

def pushRetStmt(s, loc, toks) :
    temp = di.ReturnStatement(toks[0])
    return temp

def pushParamList(s, loc, toks) :
    return [toks]

def pushUnaryExpr(s, loc, toks) :
    if len(toks) == 1 :
        return toks
    temp = di.UnOperation(toks[0], toks[1])
    return temp

def parseDataRegion(s, loc, toks) :
    temp = di.DataRegion(toks[0], toks[1], toks[2])
    return temp

def pushLeftAssocExpr(s, loc, toks) :
    opSt = []
    exSt = []
    for t in reversed(toks) :
        if isinstance(t, str) and t in [">>", ">>>", "<<", "<<<", "&", "|", "^", "+", "-", "*", "/"] :
            opSt.append(t)
        else :
            exSt.append(t)

    while opSt != [] :
        op = opSt.pop()
        if op in [">>", ">>>", "<<", "<<<", "&", "|", "^", "+", "-", "*", "/"] :
            lhs = exSt.pop()
            rhs = exSt.pop()
            temp = di.BinOperation(lhs, op, rhs)
            exSt.append(temp)

    retVal = exSt.pop()
    return [retVal]

def pushCallVar(s, loc, toks) :
    temp = di.FunctionCall(toks[0], toks[2])
    return temp

def pushCallArg(s, loc, toks) :
    return [toks]

def pushArrayVar(s, loc, toks) :
    progOrig = None
    arrName = None
    arrIndex = None

    if len(toks) == 3 :
        arrName = toks[0]
        bitlength = toks[1][1:]
        arrIndex = toks[2]
    elif len(toks) == 4 :
        progOrig = toks[0][:-1]
        arrName = toks[1]
        bitlength = toks[2][1:]
        arrIndex = toks[3]
    
    temp = di.ArrayCall(arrName, arrIndex)
    temp.length = int(bitlength, 0)
    
    if progOrig != None : temp.programOrigin = progOrig
    return [temp]

def parseFunction(s, loc, toks) :
    temp = di.Function(toks[0], toks[2], toks[3])
    return temp

lpar = pp.Literal("(")
rpar = pp.Literal(")")
shiftOpGroup = pp.oneOf(">> >>> << <<<")
andOpGroup = pp.oneOf("& | ^")
plusOpGroup = pp.oneOf("+ -")
multOpGroup = pp.oneOf("* /")
unOpGroup = pp.oneOf("!")
comparator = pp.oneOf("= > >= < <= == !=")

constant = pp.Combine(pp.Optional(pp.Literal("-")) + pp.Word(pp.hexnums)) + pp.Optional(pp.Combine(pp.Literal(":") + pp.Word(pp.hexnums)), default=":32")
tempVar = pp.Optional(pp.Combine(pp.Word(pp.alphas, pp.alphanums) + pp.Literal("."))) + pp.Word(pp.alphas, pp.alphanums + "_") + pp.Optional(pp.Combine(pp.Literal(":") + pp.Word(pp.hexnums)), default=":32")
hexConstant = pp.Combine("0x" + pp.Word(pp.hexnums)) + pp.Optional(pp.Combine(pp.Literal(":") + pp.Word(pp.hexnums)), default=":32")
label = pp.Combine(pp.Literal("L$") + pp.Word(pp.alphas, pp.alphanums + "_"))

orExpression = pp.Forward()
argList = (orExpression + pp.ZeroOrMore(pp.Suppress(pp.Literal(",")) + orExpression)).setParseAction(pushCallArg)
callVar = (tempVar + pp.Suppress(lpar) + pp.Optional(argList) + pp.Suppress(rpar)).setParseAction(pushCallVar)
arrayVar = (tempVar + pp.Suppress(pp.Literal("[")) + orExpression + pp.Suppress(pp.Literal("]"))).setParseAction(pushArrayVar)

factor = arrayVar | callVar | (label | tempVar | hexConstant | constant).setParseAction(CreateVar) | (pp.Suppress(pp.Literal("(")) + orExpression + pp.Suppress(pp.Literal(")")))

unaryExpression = ((unOpGroup + factor) | factor).setParseAction(pushUnaryExpr)
multExpression = unaryExpression + pp.ZeroOrMore(multOpGroup + unaryExpression)
multExpression.setParseAction(pushLeftAssocExpr)
plusExpression = multExpression + pp.ZeroOrMore(plusOpGroup + multExpression)
plusExpression.setParseAction(pushLeftAssocExpr)
shiftExpression = plusExpression + pp.ZeroOrMore(shiftOpGroup + plusExpression)
shiftExpression.setParseAction(pushLeftAssocExpr)
andExpression = shiftExpression + pp.ZeroOrMore(pp.Literal("&") + shiftExpression)
andExpression.setParseAction(pushLeftAssocExpr)
xorExpression = andExpression + pp.ZeroOrMore(pp.Literal("^") + andExpression)
xorExpression.setParseAction(pushLeftAssocExpr)
orExpression << (xorExpression + pp.ZeroOrMore(pp.Literal("|") + xorExpression))
orExpression.setParseAction(pushLeftAssocExpr)
ifExpression = (orExpression + pp.Optional(comparator + orExpression + pp.Literal("?") + orExpression + pp.Literal(":") + orExpression)).setParseAction(parseIfExpression)
expression = orExpression + comparator + ifExpression

retStmt = (pp.Suppress(pp.Literal("return")) + orExpression + pp.Suppress(pp.Literal(";"))).setParseAction(pushRetStmt)
exprStmt = (expression + pp.Suppress(pp.Literal(";"))).setParseAction(pushExprStmt)

stmt = retStmt | exprStmt | (callVar + pp.Suppress(pp.Literal(";")))

paramList = (factor + pp.ZeroOrMore(pp.Suppress(pp.Literal(",")) + factor)).setParseAction(pushParamList)

function = (pp.Suppress("function") + tempVar + pp.Suppress(lpar) + pp.Optional(paramList) + pp.Suppress(rpar) + pp.Suppress(pp.Literal("{")) + pp.OneOrMore(stmt) + pp.Suppress(pp.Literal("}"))).setParseAction(parseFunction)

macro = (pp.Suppress("macro") + tempVar + pp.Suppress(lpar) + pp.Optional(paramList) + pp.Suppress(rpar) + pp.Suppress(pp.Literal("{")) + pp.OneOrMore(stmt) + pp.Suppress(pp.Literal("}"))).setParseAction(parseMacro)

forloop = (pp.Suppress(pp.Literal("for")) + pp.Suppress(pp.Literal("(")) + factor + pp.Suppress(pp.Literal("from")) + factor + pp.Suppress(pp.Literal("to")) + factor + pp.Suppress(pp.Literal(")")) + pp.Suppress(pp.Literal("{")) + pp.OneOrMore(stmt) + pp.Suppress(pp.Literal("}"))).setParseAction(parseLoop)

jmpStmt = (pp.Literal("jmp") + ifExpression + pp.Suppress(pp.Literal(";"))).setParseAction(pushJumpStmt)

HeapInfo = (pp.Suppress("@Data{") + factor + pp.Suppress(",") + orExpression + pp.Suppress("~") + orExpression + pp.Suppress("};")).setParseAction(parseDataRegion)

progComponent = HeapInfo | forloop | function | macro | jmpStmt | stmt
progComponentList = pp.OneOrMore(progComponent)
program = progComponentList

def dslToAst(insts) :
    parsedProgram = program.parseString(insts, parseAll=True)

    return parsedProgram
