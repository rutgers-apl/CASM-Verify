# General
verbose = False # message verbosity
memModel = 32 # memory model uses 32-bit value model.
smtTimeout = 1000 * 60 * 5 # 1 minute
aliasAnalysis = True # Performs alias analysis to reduce memory read nodes.
tempQueryFile = "temp.z3" # This is where we will save query for bash z3.
p1File = None # File for p1
p2File = None # File for p2
z3CheckSatCommand = "(check-sat-using default)"
currentUnknownCount = 0
maxUnknownCount = 1

# For statistics
totalNodesToCompare = 0
equivNodeNum = 0
noEquivNodeNum = 0
readNodeNum = 0
indexAliasNum = 0
totalIndexAliasNum = 0
totalSmtTime = 0
totalAliasAnalysisTime = 0
totalVerificationTime = 0

def PrintStatistics() :
    print("Amount of Time Spent Verifying : %f" % (totalVerificationTime))
    print("Amount of Time Spent Alias Analysis : %f" % (totalAliasAnalysisTime))
    print("Amount of Time Spent doing SMT Query : %f" % (totalSmtTime))
    print("Total Number of Node Pairs to Compare : %d" % (totalNodesToCompare))
    print("Number of Equivalent Pairs of Nodes : %d" % (equivNodeNum))
    print("Number of Not Equivalent Pair of Nodes : %d" % (noEquivNodeNum))
    print("Number of Array Read Nodes Reduced : %d" % (readNodeNum))
    print("Number of Array Index Comparisons: %d" % (totalIndexAliasNum))


# architecture of p1 and p2
arch = 0
archDict = {"x86_64" : 0, "x86" : 1}
archDictRev = {0 : "x86_64", 1 : "x86"}
arch64BitList = [0]
arch32BitList = [1]
def Is64BitArch() :
    return arch in arch64BitList

def Is32BitArch() :
    return arch in arch32BitList

# Language for p1 and p2. This is used primarily for parsing the file. Once the files are parsed,
# everything is the same. By default, we assume p1 is dsl and p2 is asm.
p1lang = 0
p2lang = 1
plangDict = {"dsl" : 0, "asm" : 1}
plangDictRev = {0 : "dsl", 1 : "asm"}
def ProgLangArgToProgLangCode(arg) :
    if arg.lower() in plangDict :
        return plangDict[arg.lower()]
    return None

def ProgLangCodeToProgLangArg(code) :
    if arg in plangDictRev :
        return plangDictRev[arg]
    return None

# Verification Mode : Describes the behavior generating SMT query to compare between two nodes.
# Three modes:
# 1. default: Include all descendant nodes of the two comparing nodes when generating SMT query.
# 2. intersection: Include the intersection of the two comparing nodes' intersections.
# 3. hybrid: When smt query for intersection gives sat, try default mode.
verifMode = 1
verifModeDict = {"default" : 1, "intersection" : 2, "hybrid" : 3}
verifModelDictRev = {1 : "default", 2 : "intersection", 3 : "hybrid"}
def VerifModeArgToVerifModeCode(arg) :
    if arg.lower() in verifModeDict :
        return verifModeDict[arg.lower()]
    return None

def VerifModeCodeToVerifModeArg(arg) :
    if arg in verifModeDictRev :
        return verifModeDictRev[arg]
    return None

# Static function that sets up config. Just in case I may need multiple configuration...
def SetUpConfig(c, arg) :
    # Set verbosity
    c.verbose = arg.verbose

    # Set program architecture (32bit vs 64bit)
    if arg.arch != None :
        if arg.arch == "x86" : c.arch = 1
        elif arg.arch == "x86_64" : c.arch = 0
        else :
            print("%s is not an available architecture. Defaulting to x86_64" % (arg.arch))
            c.arch = 0

    # Set memory model
    if arg.mem_model != None :
        # Make sure they gave me a valid memory model.
        if arg.mem_model in [8, 32] :
            c.memModel = arg.mem_model
        else :
            print("Unsupported memory model (%d bits). Defaulting to 32-bit value" % (arg.mem_model))
            c.memModel = 32

    error_exit = False
    # Set p1 and p2 file :
    if arg.p1 == None :
        print("Command Argument Error: Please provide file for p1")
        error_exit = True
    else : c.p1File = arg.p1
    if arg.p2 == None :
        print("Command Argument Error: Please provide file for p2")
        error_exit = True
    else : c.p2File = arg.p2

    # Set p1lang and p2lang (How to parse p1 and p2 file? DSL or ASM?) :
    if arg.p1lang == None :
        print("Command Argument Warning: p1lang not specified. Assuming p1 is DSL")
        c.p1lang = 0
    else :
        p1langCode = ProgLangArgToProgLangCode(arg.p1lang)
        if p1langCode == None :
            print("Command Argument Error: Unknown p1lang code: %s" %(arg.p1lang))
            error_exit = True
        c.p1lang = p1langCode

    if arg.p2lang == None :
        print("Command Argument Warning: p2lang not specified. Assuming p2 is ASM")
        c.p2lang = 1
    else :
        p2langCode = ProgLangArgToProgLangCode(arg.p2lang)
        if p2langCode == None :
            print("Command Argument Error: Unknown p2lang code: %s" % (arg.p1lang))
            error_exit = True
        else : c.p2lang = p2langCode

    # Set up verifMode
    if arg.verif_mode != None :
        verifModeCode = VerifModeArgToVerifModeCode(arg.verif_mode)
        if verifModeCode == None :
            print("Command Argument Error: Unknown verif_mode code: %s" % (arg.verif_mode))
            error_exit = True
        else : c.verifMode = verifModeCode

    # Set up z3_check_command
    if arg.z3_check_command != None :
        c.z3CheckSatCommand = arg.z3_check_command
        
    if error_exit : assert(False)

    if arg.no_alias_analysis :
        c.aliasAnalysis = False

    if arg.timeout != None :
        c.smtTimeout = int(arg.timeout) * 1000

    if arg.max_unknown_count != None :
        c.maxUnknownCount = arg.max_unknown_count
