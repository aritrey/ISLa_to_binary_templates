import random
import re
import string



def get_random_string(length):
    letters = string.ascii_lowercase
    return ''.join(random.choice(letters) for i in range(length))

    
def expressionStartsWithNonterminal(exp):
    return re.match("^<[A-Za-z][A-Za-z0-9_\-\']*>.*", exp)
def expressionEndsWithNonterminal(exp):
    return re.match(".*<[A-Za-z][A-Za-z0-9_\-\']*>$", exp)
    
def hasMultipleNonterminal(exp):
    return re.match(".*<[A-Za-z][A-Za-z0-9_\-\']*>.*<[A-Za-z][A-Za-z0-9_\-\']*>.*", exp)
def hasNonterminal(exp):
    return re.match(".*<[A-Za-z][A-Za-z0-9_\-\']*>.*", exp)

def isNonterminal(exp):
    return re.match("<[A-Za-z][A-Za-z0-9_\-\']*>", exp)
def isTerminal(exp):
    return not re.match(".*<[A-Za-z][A-Za-z0-9_\-\']*>.*", exp)


def derivationOptionIsEpsylon(option):
    return option == ''

def findFirstTerminal(s):
    return re.split('<[A-Za-z][A-Za-z0-9_\-\']*>', s)[0]
def findLastTerminal(s):
    return re.split('<[A-Za-z][A-Za-z0-9_\-\']*>', s)[-1]


def isOnlyOneTerminalOrNonterminal(s):
    onlyTerminal = re.compile("^<[A-Za-z][A-Za-z0-9_\-\']*>$")
    withNegationOnlyNonterminal = re.compile("(<[A-Za-z][A-Za-z0-9_\-\']*>)")

    return onlyTerminal.match(s) or not withNegationOnlyNonterminal.match(s)



def findFirstNonTerminal(s):
    test =re.findall('<[A-Za-z][A-Za-z0-9_\-\']*>', s)
    return test[0]
def findAllNonTerminal(s):
    test =re.findall('<[A-Za-z][A-Za-z0-9_\-\']*>', s)
    return test
def findLastNonTerminal(s):
    return re.search('.*(<[A-Za-z][A-Za-z0-9_\-\']*>).*', s).group(1)


def getLengthOfEqualTerminalPrefix(parent, child):
    prefix = ""
    if(parent==child):
        prefixLen=len(parent) 
    else:
        if(len(parent)>len(child)):
            smallerWord=child
            longerWord=parent
        else:
            smallerWord=parent
            longerWord=child      
        while longerWord[:len(prefix)] == prefix and smallerWord[:len(prefix)] == prefix:
            prefix = longerWord[:len(prefix)+1]
        prefixLen=len(prefix)-1
    
    termParent=findFirstTerminal(parent)
    termChild=findFirstTerminal(child)
    return min(prefixLen, len(termParent), len(termChild))
    
def getLengthOfEqualTerminalSuffix(parent, child):
    suffix = ""
    if(len(parent)>len(child)):
        smallerWord=child
        longerWord=parent
    else:
        smallerWord=parent
        longerWord=child      
    while longerWord[-len(suffix):] == suffix and smallerWord[-len(suffix):] == suffix:
        suffix = longerWord[-len(suffix)+1:]
    
    termParent=findLastTerminal(parent)
    termChild=findLastTerminal(child)
    return min(len(suffix)-1, len(termParent), len(termChild))
    

def escapeString(s):
    return s.translate(str.maketrans({'"':  r'\"',
                                        #"-":  r"\-",
                                          "]":  r"\]",
                                          "\\": r"\\",
                                          "^":  r"\^",
                                          "$":  r"\$",
                                          "*":  r"\*",
                                         # ".":  r"\."
                                          }))


def hasEqualPrefix(possibleTerminal, derivationRule):
    return derivationRule[:len(possibleTerminal)]==possibleTerminal

def getBeginFromEndStackLocation(end):
    return re.search("^\((<[a-zA-z-_]+>) end\)", end).group(1)
    
def isSpezRule(str):
    return re.match("{.*<[a-zA-Z-_]+>.*}", str)


def getEndRecursiveRule(lastNonterm, recursionRules):
    pattern = re.compile(f".+{lastNonterm}")
    return list(filter(pattern.match, recursionRules))



