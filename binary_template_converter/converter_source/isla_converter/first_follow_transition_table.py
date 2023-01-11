
# copyright notice done as suggested by https://integrity.mit.edu/handbook/writing-code

# code in this file adapted from:
# https://github.com/sid24rane/LL1-parser
# last access: 23.12.2022

#MIT License
#
#Copyright (c) 2018 Siddhesh Rane
#
#Permission is hereby granted, free of charge, to any person obtaining a copy
#of this software and associated documentation files (the "Software"), to deal
#in the Software without restriction, including without limitation the rights
#to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
#copies of the Software, and to permit persons to whom the Software is
#furnished to do so, subject to the following conditions:
#
#The above copyright notice and this permission notice shall be included in all
#copies or substantial portions of the Software.
#
#THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
#OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
#SOFTWARE.





import collections
from global_defines import GlobalDefines

from isla_converter.help_functions import derivationOptionIsEpsylon, expressionStartsWithNonterminal, findFirstNonTerminal, findFirstTerminal, isOnlyOneTerminalOrNonterminal


def addFollowTableInfo(followTable, key, s, grammar):
    if key in followTable:
        temp = followTable[key]
    else:
        followTable = createFollowTable(key, grammar, followTable)
        temp = followTable[key]
    followTable[s] = followTable[s].union(temp)


def createFollowTable(s, grammar, followTable):
    if(not isOnlyOneTerminalOrNonterminal(s)):
        return {}

    for key in grammar:
        for value in grammar[key]:
            # Stelle an der erstes Auftauchen von var is
            derivationRuleCountWithS = value.find(s)
            if derivationRuleCountWithS > -1:
                if value.endswith(s):  # checke ob string als letztes in Regel kommt
                    if key != s:  # wenn es kein rekursiver aufruf ist
                        # übernimm alle Werte von createFollowTable(key) oder erstelle erst alle werte von createFollowTable(key) und übernimm dann
                        addFollowTableInfo(followTable, key, s, grammar)
                else:  # wenn s nicht als letztes in Regel
                    # finde createFirstTableForExp(Nachfolger von s)
                    valueAfterS = value[derivationRuleCountWithS+len(s):]
                    first_of_next = createFirstTableForExp(
                        valueAfterS, grammar)
                    # wenn das @ ist,
                    if derivationOptionIsEpsylon(first_of_next):
                        if key != s:
                            # übernimm alle Werte von createFollowTable(key) oder erstelle erst alle werte von createFollowTable(key) und übernimm dann
                            addFollowTableInfo(followTable, key, s, grammar)
                            # schmeiße alle epsilons aus follow table raus
                            followTable[s] = followTable[s].union(
                                first_of_next) - {'@'}
                    else:
                        # wenn das nicht @ is trags einfach ein
                        followTable[s] = followTable[s].union(first_of_next)
    return followTable




def createFollow_dict(productions):
    follow_dict = dict()
    start = "<start>"
    for lhs in productions:
        follow_dict[lhs] = set()
    follow_dict[start] = follow_dict[start].union('$')

    for lhs in productions:
        follow_dict = createFollowTable(lhs, productions, follow_dict)

    for lhs in productions:
        follow_dict = createFollowTable(lhs, productions, follow_dict)
    return follow_dict

#the non-terminals given to "excludedNonterminals" are not considered as pars of the grammar
def createFirstTableForExp(exp, grammar, excludedNonterminals=None):
    firstTable = set()
    if expressionStartsWithNonterminal(exp):
        firstNonterminal = findFirstNonTerminal(exp)
        if(excludedNonterminals and firstNonterminal in excludedNonterminals):
            return firstTable
        derivationOptions = grammar[firstNonterminal]
        for option in derivationOptions:
            if not derivationOptionIsEpsylon(option):
                recursiveTerminals = createFirstTableForExp(option, grammar,excludedNonterminals)
                firstTable = firstTable.union(recursiveTerminals)
    else:
        firstTerminal = findFirstTerminal(exp)
        firstTable = firstTable.union([firstTerminal])
    

    return firstTable


def addValToTransitionTable(s, key, tTable, val):
    if key not in tTable:
        tTable[key] = collections.OrderedDict()
    if s not in tTable[key]:
        tTable[key][s] = list()
    tTable[key][s].append(val)
    return tTable


def createTransitionTable(follow, grammar):
    table = {}
    for key in grammar:
        for value in grammar[key]:
            # table[A, b] if A->a and First(a)=b
            if value != GlobalDefines.EPSILON:
                for s in createFirstTableForExp(value, grammar):

                    table = addValToTransitionTable(s, key, table, value)
            else:
                # table[A, b] if A->a and First(a)=epsilon and Follow(a)=b
                for s in follow[key]:

                    table = addValToTransitionTable(s, key, table, value)

    

    return table


