from global_defines import GlobalDefines
from isla_converter.isla_token import Assign
from isla_converter.constraint import Constraint
from isla_converter.help_functions import expressionEndsWithNonterminal, expressionStartsWithNonterminal, findAllNonTerminal, findFirstNonTerminal, findFirstTerminal, findLastNonTerminal, findLastTerminal, getLengthOfEqualTerminalPrefix, hasEqualPrefix, hasMultipleNonterminal, hasNonterminal, isSpezRule, isTerminal
from isla_converter.first_follow_transition_table import createFirstTableForExp, createFollow_dict, createTransitionTable


#get all reachable noterms with startVar as root symbol
def getReachableNonterms(reachableList, startVar, grammar):
        derivationRules=grammar[startVar]
        for devRule in derivationRules:
            currNonterms=findAllNonTerminal(devRule)
            newReachables = list(set(currNonterms) - set(reachableList))
            reachableList.extend(newReachables)
            for newStartVar in newReachables:
                getReachableNonterms(reachableList, newStartVar, grammar)



def inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1, grammar, childPart2, isAddedFlag, addAllSpezRulesFlag,lexer):
    #connection to variable in derivation rule was found, from now on only search if this derivation works
    if(childPart1=="" and isAddedFlag[0]==False):
        wayFound=False
        waysToGo.append(connectionArr.copy())
        oldAddedFlag=isAddedFlag[0]
        isAddedFlag[0]=True
        if(inGrammarFindConnectionBetween(waysToGo,connectionArr, connectionArrEnd,arr, parent, childPart1, grammar, childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)):
            wayFound=True
        else:
            isAddedFlag[0]=oldAddedFlag
            waysToGo.pop()
        return wayFound
    if parent=="":
        return True
    if(parent[0]=="|"):
        wayFound=False
        connectionArr.append(connectionArrEnd.pop())
        if(inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd, arr, parent[1:], childPart1, grammar, childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)):
            wayFound= True
        connectionArrEnd.append(connectionArr.pop())
        return wayFound
    child=childPart1+childPart2
    transitionTable=createTransitionTable(createFollow_dict(grammar), grammar)
    parentStartsWithNonterm = expressionStartsWithNonterminal(parent)
    childStartsWithNonterm = expressionStartsWithNonterminal(child)
    if(parent==child and findFirstTerminal(parent)==parent):
        return True
    if parent.startswith("@"):
        return inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, parent[1:],  childPart1, grammar, childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)
    if child.startswith("@"):
        if(childPart1==""):
            return inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, parent,  childPart1, grammar, childPart2[1:], isAddedFlag,addAllSpezRulesFlag,lexer)
        return inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, parent,  childPart1[1:], grammar, childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)


    if(parentStartsWithNonterm and childStartsWithNonterm):
        parentNonterm = findFirstNonTerminal(parent)
        childNonterm = findFirstNonTerminal(child)
        
        
        if(parentNonterm==childNonterm):
            connectionArr.append(parentNonterm)
            nonternLen=len(parentNonterm)
            if(childPart1!=childNonterm and parentNonterm==childNonterm):
                connectionArr.append("_")
                connectionArr.append(f"({parentNonterm} end)")
            if(childPart1==""):
                canBeParsed=inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, parent[nonternLen:],childPart1, grammar,childPart2[nonternLen:], isAddedFlag,addAllSpezRulesFlag,lexer)
            else:
                canBeParsed=inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, parent[nonternLen:],childPart1[nonternLen:], grammar,childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)
            if(canBeParsed):
                return True
            else:
                connectionArr.pop()
                if(childPart1!=childNonterm and parentNonterm==childNonterm):
                        connectionArr.pop()
                        connectionArr.pop()
        else:
            possibleParentTerms = createFirstTableForExp(parentNonterm, grammar)
            possibleChildTerms = createFirstTableForExp(childNonterm, grammar)
            waysToProof=set()
        
            for pTerminal in possibleParentTerms:
                for cTerminal in possibleChildTerms:
                    if hasEqualPrefix(pTerminal, cTerminal):
                            waysToProof.update(transitionTable[parentNonterm][ pTerminal])
                    if(pTerminal=="@"):
                        waysToProof.update("@")
            if(len(waysToProof) == 0):
                return False
            wayFound=False
            for way in waysToProof:
                connectionArr.append(parentNonterm)
                if(len(waysToProof)>1 or isTerminal(way) or addAllSpezRulesFlag):
                    connectionArr.append(f"{{{paddSpezRule(way,lexer)}}}")

                connectionArrEnd.append(f"({parentNonterm} end)")
                if(inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, way+"|"+parent[len(parentNonterm):], childPart1, grammar,childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)):
                    wayFound= True
                
                connectionArrEnd.pop()
                connectionArr.pop(-1)
                if(len(waysToProof)>1 or isTerminal(way) or addAllSpezRulesFlag):
                    connectionArr.pop(-1)
            
            return wayFound
    if(not parentStartsWithNonterm and not childStartsWithNonterm):
        terminalParent = findFirstTerminal(parent)
        terminalChild = findFirstTerminal(child)
        length=getLengthOfEqualTerminalPrefix(terminalParent, terminalChild)
            

        parent=parent[length:]
        child=child[length:]
        if(parent[0]!="|"  and not expressionStartsWithNonterminal(parent)and not expressionStartsWithNonterminal(child)):
            return False
        if(childPart1==""):
            return inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1, grammar,childPart2[length:], isAddedFlag,addAllSpezRulesFlag,lexer)
        else:
            return inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1[length:], grammar,childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)


    if(parentStartsWithNonterm and not childStartsWithNonterm):
        nonterminal = findFirstNonTerminal(parent)
        
        possibleFirstTerminals=createFirstTableForExp(nonterminal, grammar)
        waysToProof=set()
        for possibleTerminal in possibleFirstTerminals:
            if hasEqualPrefix(possibleTerminal, child):
                waysToProof.update(transitionTable[nonterminal][ possibleTerminal])
            if(possibleTerminal=="@"):
                waysToProof.update("@")
        if(len(waysToProof) == 0):
            return False
            
        wayFound=False
        for way in waysToProof:
            fullWay=way+parent[len(nonterminal):]
            connectionArr.append(nonterminal)
            if(len(waysToProof)>1 or isTerminal(way) or addAllSpezRulesFlag):
                connectionArr.append(f"{{{paddSpezRule(way,lexer)}}}")
            connectionArrEnd.append(f"({nonterminal} end)")
            if(inGrammarFindConnectionBetween(waysToGo,connectionArr,connectionArrEnd,arr, way+"|"+parent[len(nonterminal):], childPart1, grammar,childPart2, isAddedFlag,addAllSpezRulesFlag,lexer)):
                 wayFound= True
            connectionArr.pop(-1)
            connectionArrEnd.pop()
            if(len(waysToProof)>1 or isTerminal(way) or addAllSpezRulesFlag):
                connectionArr.pop(-1)
        return wayFound
            
    if(not parentStartsWithNonterm and childStartsWithNonterm):
        return False
       
def addDontCareAfter(stackLocation):
    newStackLocation=[]
    for index, value in enumerate(stackLocation):
        if isSpezRule(value):
            afterNonterm=value.split(stackLocation[index+1])[1]
            for nonterm in afterNonterm:
                newStackLocation.append(nonterm)
                newStackLocation.append("_")
                newStackLocation.append(f"({nonterm} end)")
        else:
            newStackLocation.append(value)
            
def addDontCareVal(connectionArr):
    newConnectionArr=[]
    for i in range(len(connectionArr)):
        elem=connectionArr[i]
        newConnectionArr.append(elem)
        if(elem[0]=="{" and hasMultipleNonterminal(elem)):
            elem=elem[:elem.rindex(connectionArr[i+1])]
            while(hasNonterminal(elem)):
                nonterm=findFirstNonTerminal(elem)
                newConnectionArr.append(nonterm)
                newConnectionArr.append("_")
                newConnectionArr.append(f"({nonterm} end)")
                elem=elem.split(nonterm)[1]
    return newConnectionArr
    

def addDontCareValDuringRuleCreation(currRule, nonterm,connectionArr):
    if(hasMultipleNonterminal(currRule)):
        currRule=currRule.rsplit(nonterm, 1)
        
        addedRulecount=0
        while(hasNonterminal(currRule)):
            earlierNonterm=findFirstNonTerminal(currRule)
            connectionArr.append(earlierNonterm)
            connectionArr.append("_")
            connectionArr.append(f"({earlierNonterm} end)")
            elem=elem.split(earlierNonterm)[1]
            addedRulecount+3
    return addedRulecount
    
def paddSpezRule(unpaddedSpezRule, lexer):
    if(unpaddedSpezRule=="@"):
        return unpaddedSpezRule
    
    paddedSpezRule=""
    while(unpaddedSpezRule):
        if(expressionStartsWithNonterminal(unpaddedSpezRule)):
            firstNonTerm=findFirstNonTerminal(unpaddedSpezRule)
            paddedSpezRule+=firstNonTerm
            unpaddedSpezRule=unpaddedSpezRule[len(firstNonTerm):]
        else:
            firstTerm=findFirstTerminal(unpaddedSpezRule)
            paddedSpezRule+=lexer.pad_terminals([firstTerm])[0]
            unpaddedSpezRule=unpaddedSpezRule[len(firstTerm):]
    return paddedSpezRule
    
    

#keep deriving parent until child is found, if found, check on the way up if child is found in all derivation possibilities. if yes, do nothing, if no, force  rule with child to be executed with 100%.
def getSeenInfo(lexer, waysToGo,connectionArr,recursionArr, arr, parent, child, grammar,isAddedFlag,prefForRealLast,trueIndicator, flagToSetInRealLast=None):
    if(child==""):
        if(flagToSetInRealLast):
            constr=Constraint(
                var=f"{GlobalDefines.normalize(connectionArr[-1][1:-1], GlobalDefines.ISLA_RULE)}",
                varType=connectionArr[-1],
                stackLocation=addDontCareVal(connectionArr),
                structBegin=[Assign(flagToSetInRealLast, True)]
                )
            waysToGo.append(constr)
        else:
            prefVal={
                "prefArr":prefForRealLast,
                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
            }
            prefChance={
                "prefChance":1,
                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
            }
            possibleVal={
                "prefArr":prefForRealLast,
                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
            }
            constr=Constraint(
                var=f"{GlobalDefines.normalize(connectionArr[-1][1:-1], GlobalDefines.ISLA_RULE)}",
                varType=connectionArr[-1],
                stackLocation=addDontCareVal(connectionArr),
                preferedValues=prefVal,
                preferedChanche=prefChance,
                possibleValues=possibleVal,
                )
            waysToGo.append(constr)
        return 1
    if(parent==""):
        return 0
    parentEndsWithNonterm = expressionEndsWithNonterminal(parent)
    childEndsWithNonterm = expressionEndsWithNonterminal(child)
    if(parentEndsWithNonterm and childEndsWithNonterm):
        parentNonterm = findLastNonTerminal(parent)
        childNonterm = findLastNonTerminal(child)


        if(parentNonterm==childNonterm):
            if(parentNonterm in connectionArr):
                recursionArr.append(parentNonterm)


            derivationRules=grammar[childNonterm]
            addedRecursionCounter=0
            for derivationRule in derivationRules:
                if(childNonterm in derivationRule):
                    recursiveNontermOfRule=findAllNonTerminal(parent.split(parentNonterm)[0])
                    connectionArr.append(parentNonterm)
                    for recNonterm in recursiveNontermOfRule:
                        connectionArr.append(recNonterm)
                        connectionArr.append("_")
                        connectionArr.append(f"({recNonterm} end)")
                    addedRecursionCounter+=len(recursiveNontermOfRule)*3+1
                    connectionArr.append(f"${len(recursiveNontermOfRule)*3+1}")


            connectionArr.append(parentNonterm)
            nonternLen=len(parentNonterm)
            seenInfoFound=getSeenInfo(lexer, waysToGo,connectionArr,recursionArr, arr, parent[:-nonternLen], child[:-nonternLen], grammar,isAddedFlag,prefForRealLast,trueIndicator, flagToSetInRealLast)
            connectionArr.pop()
            return seenInfoFound
        else:
            waysToProof=grammar[parentNonterm]
            waysWithNonterm=[]
            totalSeenInfoCount=0

            
            for way in waysToProof:

                #HANDLE recursion <x>-><id><x><y>  
                if(parentNonterm in findAllNonTerminal(way)):
                    #__handle recursion____
                    derivationRuleWithoutRecursions=way.split(parentNonterm)
                    afterLastRecursion=derivationRuleWithoutRecursions[-1]
                    
                    connectionArr.append(parentNonterm)
                    if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                        connectionArr.append(f"{{{paddSpezRule(way,lexer)}}}")
                    seenInfoCount=getSeenInfo(lexer, waysToGo,connectionArr,recursionArr,arr,afterLastRecursion, child, grammar,isAddedFlag,prefForRealLast,trueIndicator, flagToSetInRealLast)
                    connectionArr.pop(-1)
                    if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                        connectionArr.pop(-1)
                    #____normal last rule-> the recursion is before the last element (e.g. <x>-><a><x><id> with searched=<id>)
                    if(seenInfoCount>0):
                        waysWithNonterm.append(way)
                        totalSeenInfoCount+=seenInfoCount
                        continue
                    #____no searched nonterm was found after rekursion -> search before recursion
                    else:
                        beforeLastRecursion="".join(derivationRuleWithoutRecursions[:-1])

                        #search for recursive
                        waysToGo2=[]
                        connectionArr2=[]
                        connectionArrEnd2=[]
                        arr2=[]
                        childInRecursionFound=childInParentSeen(waysToGo2,connectionArr2,connectionArrEnd2, arr2, beforeLastRecursion, child, grammar, "", [False])

                        if(childInRecursionFound):
                            for i in range(totalSeenInfoCount):
  
                                waysToGo.pop()
                            if(expressionStartsWithNonterminal(way)):
                                prefArr=createFirstTableForExp(findFirstNonTerminal(way), grammar)
                            else:
                                prefArr=[way[0]]
                            
                            #TODO: nur machen, wenn es bei parentNonterm mehr als eine derivation rule gibt
                            recursiveNontermOfRule=findAllNonTerminal(way.split(parentNonterm)[0])
                            if len(recursiveNontermOfRule)>0:
                                connectionArr.append(parentNonterm)
                                for recNonterm in recursiveNontermOfRule:
                                    connectionArr.append(recNonterm)
                                    connectionArr.append("_")
                                    connectionArr.append(f"({recNonterm} end)")
                                connectionArr.append(f"${len(recursiveNontermOfRule)*3+1}")
                            connectionArr.append(parentNonterm)
                            prefVal={
                                "prefArr":{"values":prefArr,"arrays":[],'notEqualsWithArr':[]},
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            prefChance={
                                "prefChance":1,
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            possibleVal={
                                "prefArr":{"values":prefArr,"arrays":[],'notEqualsWithArr':[]},
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            constr=Constraint(
                                var=f"{GlobalDefines.normalize(parentNonterm[1:-1], GlobalDefines.ISLA_RULE)}",
                                varType=parentNonterm,
                                preferedValues=prefVal,
                                preferedChanche=prefChance,
                                possibleValues=possibleVal,
                                stackLocation=addDontCareVal(connectionArr))

                            waysToGo.append(constr)

                            connectionArr.pop(-1)
                            return 1  

    

  
                        else:
                            continue
                    #__handle recursion END____
                            
                        
                connectionArr.append(parentNonterm)
                if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                    connectionArr.append(f"{{{paddSpezRule(way,lexer)}}}")
                #sucht nur in letztem nonterm -> TODO:nonterm davor extra prüfen bitte
                seenInfoCount=getSeenInfo(lexer, waysToGo,connectionArr,recursionArr,arr, way, child, grammar,isAddedFlag,prefForRealLast,trueIndicator, flagToSetInRealLast)
                if(seenInfoCount>0):
                    waysWithNonterm.append(way)
                    totalSeenInfoCount+=seenInfoCount
                connectionArr.pop(-1)
                if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                    connectionArr.pop(-1)

            #no fitting rule with nonterm found
            if(len(waysWithNonterm)==0):
                return 0


            #exclude rules that do not have nonterminal
            if(set(waysWithNonterm)!=set(waysToProof)):
                connectionArr.append(parentNonterm)
                possible=set()
                for way in waysWithNonterm:

    
  
                    childEndsWithNonterm
                    if(expressionEndsWithNonterminal(way)):
                        firstSet=createFirstTableForExp(findFirstNonTerminal(way),grammar)
                        possible=possible.union(firstSet)
                    else:
                        possible.add(way[0])
                prefVal={
                    "prefArr":{"values":possible,"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":[]
                }
                prefChance={
                    "prefChance":1,
                    "conditions":[]
                }
                possibleVal={
                    "prefArr":{"values":possible,"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":[]
                }
                constr=Constraint(varType=parentNonterm,preferedChanche=prefChance,preferedValues=prefVal,possibleValues=possibleVal, stackLocation=addDontCareVal(connectionArr))
                waysToGo.append(constr)
                connectionArr.pop(-1)
                return totalSeenInfoCount+1
            else:
                return totalSeenInfoCount
            

    if(not parentEndsWithNonterm and not childEndsWithNonterm):
        raise ValueError("in getSeenInfo: children with terminals not supported")

    if(parentEndsWithNonterm and not childEndsWithNonterm):
        raise ValueError("in getSeenInfo: children with terminals not supported")



  
    if(not parentEndsWithNonterm and childEndsWithNonterm):
        termParent=findLastTerminal(parent)
        return getSeenInfo(lexer, waysToGo,connectionArr,recursionArr, arr, parent[:-len(termParent)], child, grammar,isAddedFlag,prefForRealLast,trueIndicator, flagToSetInRealLast)
    

def getNontermSeenInfo(waysToGo,connectionArr,recursionArr, arr, parent, childStackLocation, childStackLocIndex, grammar,isAddedFlag,prefForRealLast,trueIndicator, flagForLast):
    if(childStackLocIndex==len(childStackLocation)):
        varType=childStackLocation[childStackLocIndex-1]
        constr=Constraint(
                    var=f"{GlobalDefines.normalize(varType, GlobalDefines.ISLA_RULE)}",
                    varType=varType,
                    stackLocation=addDontCareVal(connectionArr),
                    operation=Assign(flagForLast,True) )
        waysToGo.append(constr)
        return 1
    if(parent==""):
        return 0
    parentEndsWithNonterm = expressionEndsWithNonterminal(parent)
    currChildValue=childStackLocation[childStackLocIndex]
    if(parentEndsWithNonterm):
        parentNonterm = findLastNonTerminal(parent)
        
        if(parentNonterm==currChildValue):
            innerParentExpr=grammar[parentNonterm]
            if(childStackLocIndex+1!=len(childStackLocation) and isSpezRule(childStackLocation[childStackLocIndex+1])):
                innerParentExpr=[childStackLocation[childStackLocIndex+1][1:-1]]
            if(parentNonterm in connectionArr):
                recursionArr.append(parentNonterm)
            connectionArr.append(parentNonterm)
            
            totalSeenInfoCount=0
            waysWithNonterm=[]
            for parExpr in innerParentExpr:
                currSeenInfoFound=getNontermSeenInfo(waysToGo,connectionArr,recursionArr, arr, parExpr,   childStackLocation, childStackLocIndex+1,grammar,isAddedFlag,prefForRealLast,trueIndicator,flagForLast)
                totalSeenInfoCount+=currSeenInfoFound
                if(currSeenInfoFound>0):
                    waysWithNonterm.append(parExpr)
            if(set(waysWithNonterm)!=set(innerParentExpr)):
                possible=set()
                for way in waysWithNonterm:
                    
                    if(expressionEndsWithNonterminal(way)):
                        firstSet=createFirstTableForExp(findFirstNonTerminal(way),grammar)
                        possible=possible.union(firstSet)
                    else:
                        possible.add(way[0])
                prefVal={
                    "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': possible},"arrays":[], 'notEqualsWithArr':[]},
                    "conditions": [{"condition":trueIndicator, "isParentApplicable": True}]
                }
                prefChance={
                    "prefChance":1,
                    "conditions": [{"condition":trueIndicator, "isParentApplicable": True}]
                }
                possibleVal={
                    "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': possible},"arrays":[], 'notEqualsWithArr':[]},
                    "conditions": [{"condition":trueIndicator, "isParentApplicable": True}]
                }
                constr=Constraint(
                    var=f"{GlobalDefines.normalize(parentNonterm[1:-1], GlobalDefines.ISLA_RULE)}",
                    varType=parentNonterm,
                    stackLocation=addDontCareVal(connectionArr),
                    preferedValues=prefVal,
                    preferedChanche=prefChance,
                    possibleValues=possibleVal)
                    
                
                waysToGo.append(constr)
                return totalSeenInfoCount+1
            else:
                return totalSeenInfoCount
        else:
            waysToProof=grammar[parentNonterm]
            waysWithNonterm=[]
            totalSeenInfoCount=0
            
            
            for way in waysToProof:
                #HANDLE recursion <x>-><id><x><y>
                if(parentNonterm in findAllNonTerminal(way)):
                    #__handle recursion____
                    derivationRuleWithoutRecursions=way.split(parentNonterm)
                    afterLastRecursion=derivationRuleWithoutRecursions[-1]
                    
                    connectionArr.append(parentNonterm)
                    if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                        connectionArr.append(f"{{{way}}}")
                    # add recursion to the rule
                    recLenCounter=1
                    connectionArr.append(parentNonterm)
                    for ruleNonterms in findAllNonTerminal(way.split(parentNonterm)[0]):
                        connectionArr.append(ruleNonterms)
                        connectionArr.append("_")
                        connectionArr.append(f"({ruleNonterms} end)")
                        recLenCounter+=3
                    connectionArr.append(f"${recLenCounter}")
                    
                    connectionArr.append(parentNonterm)
                    seenInfoCount=getNontermSeenInfo(waysToGo,connectionArr,recursionArr, arr, afterLastRecursion,   childStackLocation, 0,grammar,isAddedFlag,prefForRealLast,trueIndicator,flagForLast)
                    connectionArr.pop(-1)
                    if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                        connectionArr.pop(-1)
                    for i in range(recLenCounter+1):
                        connectionArr.pop(-1)
                    if(seenInfoCount>0):
                        waysWithNonterm.append(way)
                        totalSeenInfoCount+=seenInfoCount
                        continue
                    else:
                        beforeLastRecursion="".join(derivationRuleWithoutRecursions[:-1])
                        
                        
                        recLenCounter=1
                        for ruleNonterms in findAllNonTerminal(way.split(parentNonterm)[0]):
                            connectionArr.append(ruleNonterms)
                            connectionArr.append("_")
                            connectionArr.append(f"({ruleNonterms} end)")
                            recLenCounter+=3
                        connectionArr.append(f"${recLenCounter}")
                        
                        connectionArr.append(parentNonterm)
                        waysToGo2=[]
                        connectionArr2=[]
                        connectionArrEnd2=[]
                        arr2=[]
                        childInRecursionFound=getNontermSeenInfo(waysToGo2,connectionArr2,connectionArrEnd2, arr2, beforeLastRecursion,   childStackLocation, 0,grammar,isAddedFlag,prefForRealLast,[False],flagForLast)
                        #___recursion must be applied (e.g. <x>-><id><x><a> with searched=<id>)
                        if(childInRecursionFound>0):
                            for i in range(totalSeenInfoCount):
                                waysToGo.pop()
                            if(expressionStartsWithNonterminal(way)):
                                prefArr=createFirstTableForExp(findFirstNonTerminal(way), grammar)
                            else:
                                prefArr=[way[0]]
                            
                            connectionArr.append(f"{{{way}}}")
                            
                            
                            recursiveNontermOfRule=findAllNonTerminal(way.split(parentNonterm)[0])
                            if len(recursiveNontermOfRule)>0:
                                connectionArr.append(parentNonterm)
                                for recNonterm in recursiveNontermOfRule:
                                    connectionArr.append(recNonterm)
                                    connectionArr.append("_")
                                    connectionArr.append(f"({recNonterm} end)")
                                
                                
                                connectionArr.append(f"${len(recursiveNontermOfRule)*3+1}")
                            connectionArr.append(parentNonterm)
                            
                            prefVal={
                                "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': prefArr},"arrays":[],'notEqualsWithArr':[]},
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            prefChance={
                                "prefChance":1,
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            possibleVal={
                                "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': prefArr},"arrays":[],'notEqualsWithArr':[]},
                                "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                            }
                            constr=Constraint(
                                var=f"{GlobalDefines.normalize(parentNonterm[1:-1], GlobalDefines.ISLA_RULE)}",
                                varType=parentNonterm,
                                stackLocation=addDontCareVal(connectionArr),
                                preferedValues=prefVal,
                                preferedChanche= prefChance,
                                possibleValues=possibleVal)
                                
                            waysToGo.append(constr)
                            
                            connectionArr.pop(-1)
                            return 1  
                        #searche nonterm was nowhere found in rule (e.g. <x>->a<x>|b with searched=<id>)
                        else:
                            continue
                    #__handle recursion END____
                            
                        
                #no recursion:
                connectionArr.append(parentNonterm)
                if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                    connectionArr.append(f"{{{way}}}")
                #sucht nur in letztem nonterm -> TODO:nonterm davor extra prüfen bitte
                seenInfoCount=getNontermSeenInfo(waysToGo,connectionArr,recursionArr,arr, way,   childStackLocation, 0,grammar,isAddedFlag,prefForRealLast,trueIndicator,flagForLast)
                if(seenInfoCount>0):
                    waysWithNonterm.append(way)
                    totalSeenInfoCount+=seenInfoCount
                connectionArr.pop(-1)
                if(hasMultipleNonterminal(way) or len(waysToProof)>1):
                    connectionArr.pop(-1)
            #no fitting rule with nonterm found
            if(len(waysWithNonterm)==0):
                return 0
            
            #exclude rules that do not have nonterminal
            if(set(waysWithNonterm)!=set(waysToProof)):
                possible=set()
                for way in waysWithNonterm:
                    
                    if(expressionEndsWithNonterminal(way)):
                        firstSet=createFirstTableForExp(findFirstNonTerminal(way),grammar)
                        possible=possible.union(firstSet)
                    else:
                        possible.add(way[0])
                prefVal={
                    "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': possible},"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                }
                prefChance={
                    "prefChance":1,
                    "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                }
                possibleVal={
                    "prefArr":{"values":{   'arrays': [],'notEqualsWithArr': [], 'values': possible},"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":[{"condition":trueIndicator, "isParentApplicable": True}]
                }
                constr=Constraint(
                    var=f"{GlobalDefines.normalize(parentNonterm[1:-1], GlobalDefines.ISLA_RULE)}",
                    varType=parentNonterm,
                    stackLocation=addDontCareVal(connectionArr),
                    preferedValues=prefVal,
                    preferedChanche= prefChance,
                    possibleValues=possibleVal)
                waysToGo.append(constr)
                return totalSeenInfoCount+1
            else:
                return totalSeenInfoCount
            
    #nur child endet mit nonterminal
    if(not parentEndsWithNonterm):
        termParent=findLastTerminal(parent)
        return getNontermSeenInfo(waysToGo,connectionArr,recursionArr,arr, parent[:-len(termParent)],   childStackLocation, childStackLocIndex,grammar,isAddedFlag,prefForRealLast,trueIndicator,flagForLast)




def childInParentSeen(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1, grammar, childPart2, isAddedFlag):
    #connection to variable in derivation rule was found, from now on only search if this derivation works
    if(childPart1=="" and isAddedFlag[0]==False):
        return True


    if parent=="":
        return True

    if(parent[0]=="|"):
        connectionArr.append(connectionArrEnd.pop())
        if(childInParentSeen(waysToGo,connectionArr,connectionArrEnd, arr, parent[1:], childPart1, grammar, childPart2, isAddedFlag)):
            return True
        else:
            connectionArrEnd.append(connectionArr.pop())
            return False

    child=childPart1+childPart2
    transitionTable=createTransitionTable(createFollow_dict(grammar), grammar)
    parentStartsWithNonterm = expressionStartsWithNonterminal(parent)
    childStartsWithNonterm = expressionStartsWithNonterminal(child)


    if(parent==child and findFirstTerminal(parent)==parent):
        return True
        
    if(parentStartsWithNonterm and childStartsWithNonterm):
        parentNonterm = findFirstNonTerminal(parent)
        childNonterm = findFirstNonTerminal(child)


        if(parentNonterm==childNonterm):
            connectionArr.append(parentNonterm)
            nonternLen=len(parentNonterm)
            if(childPart1!=childNonterm and parentNonterm==childNonterm):
                connectionArr.append("_")
                connectionArr.append(f"({parentNonterm} end)")
                
            if(childPart1==""):
                canBeParsed=childInParentSeen(waysToGo,connectionArr,connectionArrEnd,arr, parent[nonternLen:],childPart1, grammar,childPart2[nonternLen:], isAddedFlag)
            else:
                canBeParsed=childInParentSeen(waysToGo,connectionArr,connectionArrEnd,arr, parent[nonternLen:],childPart1[nonternLen:], grammar,childPart2, isAddedFlag)
            if(canBeParsed):
                return True
            else:

                connectionArr.pop()
                if(childPart1!=childNonterm and parentNonterm==childNonterm):
                        connectionArr.pop()
                        connectionArr.pop()
        else:

            possibleParentTerms = createFirstTableForExp(parentNonterm, grammar)

            waysToProof=set()

            for pTerminal in possibleParentTerms:
                waysToProof.update(transitionTable[parentNonterm][ pTerminal])

            if(len(waysToProof) == 0):
                return False

            for way in waysToProof:
                if(childInParentSeen(waysToGo,connectionArr,connectionArrEnd,arr, way+"|"+parent[len(parentNonterm):], childPart1, grammar,childPart2, isAddedFlag)):
                    return True

            return False



    if(not parentStartsWithNonterm and not childStartsWithNonterm):
        terminalParent = findFirstTerminal(parent)
        terminalChild = findFirstTerminal(child)
        length=getLengthOfEqualTerminalPrefix(terminalParent, terminalChild)


        parent=parent[length:]
        child=child[length:]
        
        if(parent[0]!="|"  and not expressionStartsWithNonterminal(parent)and not expressionStartsWithNonterminal(child)):
            return False

        if(childPart1==""):
            return childInParentSeen(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1, grammar,childPart2[length:], isAddedFlag)
        else:
            return childInParentSeen(waysToGo,connectionArr,connectionArrEnd, arr, parent, childPart1[length:], grammar,childPart2, isAddedFlag)


    if(parentStartsWithNonterm and not childStartsWithNonterm):
        nonterminal = findFirstNonTerminal(parent)

        possibleFirstTerminals=createFirstTableForExp(nonterminal, grammar)


        waysToProof=set()#set (ohne duplikate)
        for possibleTerminal in possibleFirstTerminals:
            if hasEqualPrefix(possibleTerminal, child):
                waysToProof.update(transitionTable[nonterminal][ possibleTerminal])
            if(possibleTerminal==GlobalDefines.EPSILON):
                waysToProof.update(GlobalDefines.EPSILON)
        if(len(waysToProof) == 0):
            return False
            
        for way in waysToProof:
            connectionArr.append(nonterminal)
            if(len(waysToProof)>1 or isTerminal(way)):
                connectionArr.append(f"{{{way}}}")
            #MARKED
            connectionArrEnd.append(f"({nonterminal} end)")
            if(childInParentSeen(waysToGo,connectionArr,connectionArrEnd,arr, way+"|"+parent[len(nonterminal):], childPart1, grammar,childPart2, isAddedFlag)):
                return True
            else:
                connectionArr.pop(-1)
                connectionArrEnd.pop()
                if(len(waysToProof)>1):
                    connectionArr.pop(-1)
        return False


    if(not parentStartsWithNonterm and childStartsWithNonterm):
        return childInParentSeen(waysToGo,connectionArr,connectionArrEnd,arr, parent[1:], childPart1, grammar, childPart2,isAddedFlag)


def applyInsideOrAfter(structuralConstraints, var, predicat):
    for constr in structuralConstraints:
        if(constr["operation"]=="inside" and constr["var1"]==var):
            return constr["var2"]
        if(constr["operation"]=="before" and constr["var2"]==var):
            return constr["var1"]
    quantorExp=predicat
    while quantorExp:
        if(quantorExp.isStructuralConstraint(quantorExp.operation)):
            if(not quantorExp.upperQuantorExpression or quantorExp.upperQuantorExpression.coordinatingConjunction=="and"):
                if(quantorExp.operation=="inside" and quantorExp.var1==var):
                    return quantorExp.var2
                if(quantorExp.operation=="before" and quantorExp.var2==var):
                    return quantorExp.var1
        quantorExp=quantorExp.upperQuantorExpression
    return None
def findPathToVar(structuralConstraints,lexer, arr, predicate, var, grammar, parent="start", addAllSpezRulesFlag=True):
    varOnWay=[]
    predicate.getVariablesOnWay(var,varOnWay)
    findPathToVarWithoutStructural(lexer, arr, predicate, var, grammar, parent, addAllSpezRulesFlag)
def findPathToVarWithoutStructural(lexer, arr, predicate, var, grammar, parent, addAllSpezRulesFlag):
    if(predicate==None):
        return
    if(predicate.hasVariable(var)):
        element=predicate.element
        if(predicate.elemName==var):
            
            if(predicate.containing==parent):
                arr.append(element)
                
            else:
                findPathToVarWithoutStructural(lexer, arr, predicate.upperQuantorExpression, predicate.containing,grammar,parent,addAllSpezRulesFlag)
                arr.append("_")
                arr.append(element)
                
        else:
            connectionArray =[]
            connectionArrayEnd =[]
            myArr=[]
            waysToGo=[]
            afterVar=predicate.getSpezificationAfter(var)
            untilVar=predicate.getSpezificationUntil(var)
            if(predicate.containing==parent):
                inGrammarFindConnectionBetween(waysToGo,myArr,connectionArray,connectionArrayEnd, element,untilVar,grammar,afterVar,[False],addAllSpezRulesFlag,lexer)
            else:
                
                findPathToVarWithoutStructural(lexer, arr, predicate.upperQuantorExpression, predicate.containing, grammar,parent,addAllSpezRulesFlag)
                arr.append("_")
                inGrammarFindConnectionBetween(waysToGo,myArr,connectionArray,connectionArrayEnd, element, untilVar,grammar,afterVar,[False],addAllSpezRulesFlag,lexer)
  
            for way in waysToGo:
                for elem in way:
                    arr.append(elem)
    else:
        findPathToVarWithoutStructural(lexer, arr, predicate.upperQuantorExpression, var, grammar,parent, addAllSpezRulesFlag)
