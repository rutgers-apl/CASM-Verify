import sys

reset = "\u001b[0m"
bold = "\u001b[1m"
underline = "\u001b[4m"

# Color
red = "\u001b[31m"
green = "\u001b[32m"
black = "\u001b[30m"

# Cursor navigation
def Up(c) :
    return "\u001b[%dA" % (c)

def Down(c) :
    return "\u001b[%dB" % (c)

def Right(c) :
    return "\u001b[%dC" % (c)

def Left(c) :
    return "\u001b[%dD" % (c)

def ClearScreen(c) :
    return "\u001b[%dJ" % (c)

def ClearLine(c) :
    return "\u001b[%dK" % (c)

def SavePosition(n) :
    return "\u001b[%s" % (n)

def LoadPosition(n) :
    return "\u001b[%s" % (n)

def Print(s) :
    sys.stdout.write(s)
    sys.stdout.flush()
    return

def PrintOnThisLineBold(s) :
    Print("%s%s%s%s%s" % (Left(1000), ClearLine(0), bold, s, reset))
    return

def PrintOnThisLine(s) :
    Print("%s%s%s" % (Left(1000), ClearLine(0), s))
    return

def PrintFromLeft(s, l) :
    Print("%s%s%s" % (Left(l), ClearLine(0), s))
    return
