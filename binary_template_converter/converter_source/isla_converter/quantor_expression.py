


import copy
import math
import re
from typing import Dict, List
from isla_converter.first_follow_transition_table import createFirstTableForExp, createFollow_dict, createFollowTable
from global_defines import GlobalDefines
from isla_converter.functions_for_constraint_creation import findPathToVar, getSeenInfo, getReachableNonterms
from isla_converter.help_functions import derivationOptionIsEpsylon, expressionEndsWithNonterminal, expressionStartsWithNonterminal, findAllNonTerminal, findFirstNonTerminal, findFirstTerminal, findLastNonTerminal, getBeginFromEndStackLocation, getEndRecursiveRule, isSpezRule
from isla_converter.isla_token import *
from isla_converter.constraint import Constraint


class QuantorExpression(object):
    def __init__(self,counter,upperQuantorExpression, quantor, element, elemName, spezification, containing,var1,var2,operation,coordinatingConjunction): 
        self.counter=counter
        self.upperQuantorExpression=upperQuantorExpression
        self.quantor = quantor
        self.element = element
        self.elemName = elemName
        self.spezification = spezification
        self.containing = containing
        self.var1=var1
        self.var2=var2
        self.operation=operation
        self.coordinatingConjunction=coordinatingConjunction
    
    def getSpezToAdd(self, fullQuantorExpression,spezRules, universalLexer):#fullQuantorExpression:list[Constraint]
        for constr in fullQuantorExpression:
            stackLocations=constr.stackLocation
            if(constr.stackLocation):
                firstVal=constr.stackLocation[0]
                if(type(firstVal)!=list):
                    stackLocations=[constr.stackLocation]
            
            for stackLocation in stackLocations:
                for index, potSpez in enumerate(stackLocation):
                    if(isSpezRule(potSpez)):
                        parentNonterm=stackLocations[0][index-1]
                        normalizedNonterm=GlobalDefines.normalize(parentNonterm, GlobalDefines.NON_TERMINAL)

                        if(not (normalizedNonterm in spezRules)):
                            spezRules[normalizedNonterm]=set()
                        spezRules[normalizedNonterm].add(potSpez)

    def hasVariable(self,var):
        if(self.spezification):
            varsInSpez = re.findall('\{<[A-Za-z][A-Za-z0-9_-]*> ([A-Za-z][A-Za-z0-9_-]*)\}', self.spezification) 
            return (var in varsInSpez) or self.elemName==var
        return self.elemName==var
        
    def getSpecificationWithoutVariables(self):
        return re.sub(r'\{(<[A-Za-z][A-Za-z0-9_-]*>) [A-Za-z][A-Za-z0-9_-]*\}',r"\1", self.spezification)

    def getVariablesOnWay(self,var,arr):
        if(self.hasVariable(var)):
            arr.append((var,self.counter))
            if(self.elemName!=var):
                arr.append((self.elemName,self.counter))
            searchValueForRecursion=self.containing
        else:
            searchValueForRecursion=var
        
        if(self.upperQuantorExpression):
            self.upperQuantorExpression.getVariablesOnWay(searchValueForRecursion,arr)

    def getQuantorOfVariable(self, var):
        if(self.hasVariable(var)):
            return self.quantor
        return self.upperQuantorExpression.getQuantorOfVariable(var)


    #outputs a relation when known that var1 and var2 are in the same constraint
    def getRelation(self, var1, var2, originalVar1, originalVar2,originalVar1Quantor, originalVar2Quantor):

        varsInSpez = re.findall('\{<[A-Za-z][A-Za-z0-9_-]*> ([A-Za-z][A-Za-z0-9_-]*)\}', self.spezification)
        if(var1 in varsInSpez and var2 in varsInSpez):
            if(varsInSpez.index(var1)>varsInSpez.index(var2)):
                if(var1==originalVar1 and var2 == originalVar2):
                    return Wellformed(originalVar2,originalVar1)
                return Inside(originalVar1, originalVar2, originalVar1Quantor, originalVar2Quantor, self.counter)#var1 is in var2
            if(varsInSpez.index(var1)<varsInSpez.index(var2)):
                if(var1==originalVar1 and var2 == originalVar2):
                    return Wellformed(originalVar1,originalVar2)
                return Inside(originalVar2, originalVar1, originalVar2Quantor, originalVar1Quantor, self.counter)#var1 is in var2
        return None
        

    def getQuantorWithSpezifiedVariable(self, var ):
        currQuantorExpr=self
        while currQuantorExpr:
            if(currQuantorExpr.hasVariable(var)):
                return currQuantorExpr
            currQuantorExpr=currQuantorExpr.upperQuantorExpression
            


    def findConnectionBetweenVar1And2(self, applicableOptions, varOnWay1,varOnWay2, var1, var2):
        if(applicableOptions==(True,False,False,False)):#var1loc(outside) in var on way1 
                varNotSeenInVarOnWay=var2
                varInWay=var1
                otherWay=varOnWay2
        elif(applicableOptions==(False,True,False,False)):#var2loc(inside) in var on way1 
                varNotSeenInVarOnWay=var1
                varInWay=var2
                otherWay=varOnWay1
        elif(applicableOptions==(False,False,True,False)):#var1loc(outside) in var on way2
                varNotSeenInVarOnWay=var1
                varInWay=var2
                otherWay=varOnWay2
        elif(applicableOptions==(False,False,False,True)):#var1loc(inside) in var on way2
                varNotSeenInVarOnWay=var2
                varInWay=var1
                otherWay=varOnWay1
        else: 
            raise ValueError("please rewrite your constraint so that each variable used in the equation in the quantifier free core is in a different quantifier")
        currQuantorExpr=self.getQuantorWithSpezifiedVariable(varNotSeenInVarOnWay)
        allVarOfCurrQuantorExp=currQuantorExpr.getAllVariables()
        connectionBetweenVar1And2=list((set(allVarOfCurrQuantorExp) & set([x[0] for x in otherWay])))
        commonParent=None
        connectionBetweenLocations=None
        for var in connectionBetweenVar1And2:
            if(currQuantorExpr.elemName==var):
                commonParent=var
            else:
                connectionBetweenLocations=var
        return commonParent, connectionBetweenLocations,currQuantorExpr, varNotSeenInVarOnWay,varInWay




    def getApplicableStructuralConstraintVariable(self,varOnWay1,varOnWay2, var1Origin, var2Origin, var1, var2, operation):
        isApplicable1=next((item for item in varOnWay1 if item[0] == var1),None)
        isApplicable2=next((item for item in varOnWay2 if item[0] == var2),None)
        isApplicable3=next((item for item in varOnWay1 if item[0] == var2),None)#self.var2 in varOnWay1
        isApplicable4=next((item for item in varOnWay2 if item[0] == var1),None)
        applicableOptions=(isApplicable1!=None,isApplicable2!=None,isApplicable3!=None,isApplicable4!=None)
        

        firstVar=self.getFirstVariableInExpression(var1,var2, operation)

        #only if at least one variable of the location is in a stacklocation of the equation, there can be a connection
        if(applicableOptions==(False,False,False,False) ):
            return

        var1QuantorInvolved=varOnWay1[0][1]
        var2QuantorInvolved=varOnWay2[0][1]
        reversedInside=True
        if(firstVar==var1 and var1QuantorInvolved<=var2QuantorInvolved) or (firstVar==var2 and var2QuantorInvolved<=var1QuantorInvolved):
            reversedInside=False
        if(applicableOptions==(True,False,True,False)):
            currQuantorExpr=self.getQuantorWithSpezifiedVariable(isApplicable3[0]) 
            commonParentConstrNr=currQuantorExpr.counter
            commonParentConstrVar=currQuantorExpr.elemName
            if operation=="inside":
                return Inside(var1Origin, var2Origin,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar, False) 
            elif operation=="before":
                return Before(var1Origin, var2Origin,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar, True) 
            else:
                raise ValueError("Not Impl1")  
        elif(applicableOptions==(False,True,False,True)):#normal orientation
            currQuantorExpr=self.getQuantorWithSpezifiedVariable(isApplicable2[0]) 
            commonParentConstrNr=currQuantorExpr.counter
            commonParentConstrVar=currQuantorExpr.elemName
            if operation=="inside":
                return Inside(var2Origin, var1Origin,var2QuantorInvolved,var1QuantorInvolved,commonParentConstrNr,commonParentConstrVar, False) 
            elif operation=="before":
                return Before(var2Origin, var1Origin,var2QuantorInvolved,var1QuantorInvolved,commonParentConstrNr,commonParentConstrVar, True) 
            else:
                raise ValueError("Not Impl1")  
        elif(applicableOptions==(True,True,False,False) ):
            commonParentConstrNr=isApplicable2[1]
            commonParentConstrVar=isApplicable2[0]   
            if operation=="inside":
                return Inside(var1Origin,var2Origin,var1QuantorInvolved,var2QuantorInvolved, commonParentConstrNr,commonParentConstrVar, reversedInside) 
            elif operation=="before":
                return Before(var1Origin,var2Origin,var1QuantorInvolved,var2QuantorInvolved, commonParentConstrNr,commonParentConstrVar, not reversedInside) 
            else:
                raise ValueError("Not Impl1")  
        elif(applicableOptions==(False,False,True,True)):
            commonParentConstrNr=isApplicable3[1]
            commonParentConstrVar=isApplicable3[0]

            if(reversedInside):
                commonParentConstrNr=isApplicable4[1]
                commonParentConstrVar=isApplicable4[0]

            if operation=="inside":
                # var2 in subtree of var1, si commonParentConstr is var1
                return Inside(var2Origin,var1Origin,var2QuantorInvolved,var1QuantorInvolved, commonParentConstrNr,commonParentConstrVar,reversedInside) 
            if operation=="before":
                return Before(var2Origin,var1Origin,var2QuantorInvolved,var1QuantorInvolved, commonParentConstrNr,commonParentConstrVar,reversedInside) 
            else:
                raise ValueError("Not Impl2")
        else:#only one variable is found in a stacklocation
            commonParent, connectionBetweenVarInWayAndNotSeen,currQuantorExpr,varNotSeenInVarOnWay,varInWay=self.findConnectionBetweenVar1And2(applicableOptions,varOnWay1,varOnWay2, var1, var2)

            if(bool(commonParent)):
                connectionBetweenVar1And2QuantorNr=currQuantorExpr.counter
                firstVar=currQuantorExpr.getFirstVariableInExpression(connectionBetweenVarInWayAndNotSeen,varNotSeenInVarOnWay,operation)
                varIsInWay1=varInWay in [x[0] for x in varOnWay1]

                switchTuple=(operation,firstVar,varIsInWay1)

                if(switchTuple==("inside",varNotSeenInVarOnWay, True)):
                        return Inside(var1Origin, var2Origin,var1QuantorInvolved,var2QuantorInvolved,connectionBetweenVar1And2QuantorNr,commonParent ,reversedInside)
                elif(switchTuple==("inside",varNotSeenInVarOnWay, False)):
                        return Inside(var2Origin, var1Origin,var2QuantorInvolved,var1QuantorInvolved,connectionBetweenVar1And2QuantorNr,commonParent ,reversedInside)
                elif(switchTuple==("inside",connectionBetweenVarInWayAndNotSeen, True)):
                        return Inside(var1Origin,var2Origin,var1QuantorInvolved,var2QuantorInvolved,connectionBetweenVar1And2QuantorNr,commonParent,reversedInside )
                elif(operation=="inside"):
                        raise Exception("getFirstVariableInExpression went wrong") 
                elif(operation!="inside"):
                        raise Exception("getApplicableStructuralConstraint only for 'inside' specified") 



    def getStructureViaExpressions(self,var1, var2, originalVar1, originalVar2, originalVar1Quantor, originalVar2Quantor):
        is1=self.hasVariable(var1)
        is2=self.hasVariable(var2)

        matchVar=(is1,is2)
        if(matchVar==(True,True)):
                return self.getRelation(var1, var2, originalVar1, originalVar2,originalVar1Quantor, originalVar2Quantor) #wird das ggf noch komplexer?
        elif(matchVar==(True,False)):
                firstVar=self.containing
                secondVar=var2
        elif(matchVar==(False,True)):
                firstVar=var1
                secondVar=self.containing
        elif(matchVar==(False,False)):
                firstVar=var1
                secondVar=var2


        if self.upperQuantorExpression:
            return self.upperQuantorExpression.getStructureViaExpressions(firstVar, secondVar, originalVar1, originalVar2,originalVar1Quantor, originalVar2Quantor)

    def getQuantorExprStructure(self,smallestConstraintNr,varOnWay1,varOnWay2):
        allVarUpper=self.upperQuantorExpression.getAllVariables()
        allVarUpper.append(self.upperQuantorExpression.elemName)

        downerQuantorExpr=self
        downerQuantorExprNr=downerQuantorExpr.counter
        while downerQuantorExprNr>smallestConstraintNr:
            if(downerQuantorExpr.containing in allVarUpper):
                
                varOnWay1List=list(item[0] for  item in varOnWay1 if item[1] == downerQuantorExprNr)
                varOnWay2List=list(item[0] for  item in varOnWay2 if item[1] == downerQuantorExprNr)



                if varOnWay1List!=[]:
                    return Inside(varOnWay1List[0],self.containing,downerQuantorExprNr, smallestConstraintNr )
                if varOnWay2List!=[]:
                    return Inside(varOnWay2List[0],self.containing,downerQuantorExprNr, smallestConstraintNr )

            downerQuantorExpr=self.upperQuantorExpression
            downerQuantorExprNr=downerQuantorExpr.counter

        
    #returns structural relation or variables
    def getStructuralInformationVariables(self,var1, var2,structuralConstraintsSeen):
            varOnWay1=[]
            varOnWay2=[]
            self.getVariablesOnWay(var1,varOnWay1)
            self.getVariablesOnWay(var2,varOnWay2)
            for constr in structuralConstraintsSeen:
                structuralInformation= self.getApplicableStructuralConstraintVariable(varOnWay1,varOnWay2, var1, var2,constr["var1"], constr["var2"],constr["operation"])
                if(structuralInformation):
                    return structuralInformation
            return None
    
    def hasSpez(self):
        return self.spezification!=None
    
    def getVarType(self, var):
        if(self.hasVariable(var)):
            if(self.elemName==var):
                return self.element
            else:
                return re.search(f'\{{(<[A-Za-z][A-Za-z0-9_-]*>) {var}}}', self.spezification).group(1)
        else:
            if(self.upperQuantorExpression):
                return self.upperQuantorExpression.getVarType(var)
            else:
                return str

    def isStructuralConstraint(self, constr):
        return constr=="inside" or constr=="before"


    def findAllStructuralConstraints(self, structuralConstraints):
        if(self.containing!="start"):
            structuralConstraints.append({"operation":"inside","var1":self.elemName,"var2":self.containing})
        if(self.operation=="inside" or self.operation=="before"):
            structuralConstraints.append({"operation":self.operation,"var1":self.var1,"var2":self.var2})
        if(self.upperQuantorExpression):
            self.upperQuantorExpression.findAllStructuralConstraints(structuralConstraints)



    def findStructuralInfoOfVariables(self,var1IsString,var2IsString,structuralConstraints):
        if(len(structuralConstraints)<=0):
            raise ValueError("no connection Found")
        varOnWay2=[]
        varOnWay1=[]
        giveToVar1=self.var1
        giveToVar2=self.var2


        if(not var1IsString):
            self.getVariablesOnWay(self.var1,varOnWay1)
            varOnWay1 = varOnWay1[::-1]
        else:
            if(len(structuralConstraints)>0):
                self.getVariablesOnWay(self.var2,varOnWay2)
                
                for structuralConstr in structuralConstraints:
                    var1=any(i[0]==structuralConstr["var1"] for i in varOnWay2)
                    var2=any(i[0]==structuralConstr["var2"] for i in varOnWay2)
                    if(var1 and var2 and structuralConstr["operation"]=="inside"):#bost quantors are for one constr
                        return Inside(structuralConstr["var1"],self.var2,1,0,0,structuralConstr["var2"], False )
                    if(var1 or var2):
                        giveToVar1= structuralConstraints[0]["var2"]  if var1 else structuralConstraints[0]["var1"] 
                        break

                self.getVariablesOnWay(giveToVar1,varOnWay1)
                varOnWay1 = varOnWay1[::-1]
        if(not var2IsString):
            self.getVariablesOnWay(self.var2,varOnWay2)
            varOnWay2 = varOnWay2[::-1]
        else:
            print(structuralConstraints)
            if(len(structuralConstraints)>0):
                               
                for structuralConstr in structuralConstraints:
                    var1=any(i[0]==structuralConstr["var1"] for i in varOnWay1)
                    var2=any(i[0]==structuralConstr["var2"] for i in varOnWay1)
                    if(var1 and var2 and structuralConstr["operation"]=="inside"):#bost quantors are for one constr
                        return Inside(self.var1,structuralConstr["var2"],1,0,0,structuralConstr["var2"], False )
                    if(var1 or var2):
                        giveToVar2= structuralConstraints[0]["var2"]  if var1 else structuralConstraints[0]["var1"] 
                        break

                self.getVariablesOnWay(giveToVar2,varOnWay2)
                varOnWay2 = varOnWay2[::-1]

        
        if(self.getIsStringInfo(giveToVar1)[1] or self.getIsStringInfo(giveToVar2)[1]):
            raise ValueError("no relation between variables found")

        #check if leftmost upper structural relation or leftmost upper structural relation 
        structuralRelationVariables=self.getStructuralInformationVariables(giveToVar1, giveToVar2,structuralConstraints)
        if(structuralRelationVariables==None):
            raise ValueError("no structural relation of variable was found. The parser generator can not handle this")

        return structuralRelationVariables
 

    def getIsStringInfo(self, var):
        varIsString=re.match('"(.*)"', var)
        varString=None
        if(varIsString):
            varString=varIsString.group(1)
        return varString, varIsString


    def makeBasisConstraint(self, grammar,lexer, structuralConstraints):


        if(self.isStructuralConstraint(self.operation)):
            return self.upperQuantorExpression.makeBasisConstraint( grammar,lexer, structuralConstraints)

        firstQuantor=self.upperQuantorExpression.quantor
        secondQuantor=self.quantor

        #find out if one of the two variables is a string
        var1String, var1IsString=self.getIsStringInfo(self.var1)
        var2String, var2IsString=self.getIsStringInfo(self.var2)

        structuralRelationVariables=self.findStructuralInfoOfVariables(var1IsString,var2IsString,structuralConstraints)
        
        yIsInsideX=structuralRelationVariables.isReverseRelation()
        
        varUpper=structuralRelationVariables.getVarUpper()
        varDowner=structuralRelationVariables.getVarDowner()
        upperElem=structuralRelationVariables.getUpperElem()
        stackLocationUpper=[]
        findPathToVar(structuralConstraints,lexer, stackLocationUpper, self, varUpper, grammar)
        stackLocationDowner=[]
        findPathToVar(structuralConstraints,lexer, stackLocationDowner, self, varDowner, grammar)

        if(yIsInsideX):
            upper=varUpper
            varUpper= varDowner
            varDowner=upper
            locUpper= stackLocationUpper
            stackLocationUpper= stackLocationDowner
            stackLocationDowner=locUpper
        

        matchVar=(firstQuantor,secondQuantor,var1IsString!=None,var2IsString!=None,type(structuralRelationVariables),yIsInsideX)
        matchVarWithoutStructuralRelation=(firstQuantor,secondQuantor,var1IsString!=None,var2IsString!=None,yIsInsideX)
        forall="∀"
        exists="∃"
        if(var1IsString!=None and var2IsString!=None):
                raise ValueError('two strings are compared with each other. You shoulkd use at least one variable')




        elif(matchVarWithoutStructuralRelation==(forall, forall,False,True,False) or matchVarWithoutStructuralRelation==(forall, forall,True,False,False) or matchVarWithoutStructuralRelation==(forall, forall,False,True,True) or matchVarWithoutStructuralRelation==(forall, forall,True,False,True)):
                varString=var2String if var2IsString else var1String
                allValuesPrefered=f"all_{varDowner}_prefered"
                upperStack=f"{varUpper}_stack"
                prefStack=f"{varDowner}_pref_stack"
                additional_global_info=[ValAsStrgStack(prefStack,varString)]

                if(self.operation=="="):
                    prefVal={
                        "prefArr": {"values":[varString],"arrays":[], 'notEqualsWithArr':[]},
                        "conditions":[]
                    }
                    prefChance={
                        "prefChance":1,
                        "conditions":[]
                    }
                    possibleVal={
                        "prefArr": {"values":[varString],"arrays":[], 'notEqualsWithArr':[]},
                        "conditions":[]
                    }
                elif(self.operation=="!="):
                    prefVal={
                        "prefArr": {"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]},
                        "conditions":[]
                    }
                    prefChance={
                        "prefChance":1,
                        "conditions":[]
                    }
                    possibleVal={
                        "prefArr": {"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]},
                        "conditions":[]
                    }
                    
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")


                if((yIsInsideX and self.spezification!=None) or (not yIsInsideX and self.upperQuantorExpression.spezification!=None)):
                    stackLocationUpperElem=[]
                    findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)

                    return(
                        [Constraint(
                            var=upperElem,
                            varType=self.getVarType(upperElem),
                            stackLocation=stackLocationUpperElem,
                            globalInfo=additional_global_info if self.operation=="!=" else None,
                            structEnd=[RemoveFromStackAsContainingNonterm(stackName=upperStack, nonTermType=self.getVarType(varUpper))] if (type(structuralRelationVariables)==Inside)  else None,
                            trueIndicator=allValuesPrefered),
                        
                        Constraint(
                            var=varUpper,
                            varType=self.getVarType(varUpper),
                            globalInfo=[ VarBool(allValuesPrefered),StackValId(upperStack)],
                            stackLocation=stackLocationUpper,
                            operation=AddToStackWithId(upperStack,This(varUpper))),

                        Constraint(
                            var=varDowner,
                            varType=self.getVarType(varDowner),
                            stackLocation=stackLocationDowner,
                            preferedValues=prefVal,
                            preferedChanche=prefChance,
                            possibleValues=possibleVal,
                            operation=Conditional(Not(Equals(This(varDowner),String_Token(varString))),
                            Assign(allValuesPrefered,False),None))
                        ]
                    )
                else:
                    return(
                        [Constraint(var=varUpper,varType=self.getVarType(varUpper),globalInfo=[ VarBool(allValuesPrefered),StackValId(upperStack)],stackLocation=stackLocationUpper,operation=AddToStackWithId(upperStack,This(varUpper)),structEnd= [RemoveFromStackWithId(upperStack)]if (type(structuralRelationVariables)==Inside)  else None,
                        trueIndicator=allValuesPrefered) ,

                        Constraint(var=varDowner,varType=self.getVarType(varDowner),stackLocation=stackLocationDowner,preferedValues=prefVal,preferedChanche=prefChance,possibleValues=possibleVal,operation=Conditional(Not(Equals(This(varDowner),String_Token(varString))),Assign(allValuesPrefered,False),None))
                        ])
        elif(matchVarWithoutStructuralRelation==(forall, forall,False,False,False)) or matchVarWithoutStructuralRelation==(forall, forall,False,False,True):
                
                prefChanceDowner={
                "prefChance":1,
                "conditions":[]
                }
                allValuesPrefered=f"all_{varDowner}_prefered"
                upperStack=f"{varUpper}_stack"
                if("_" in stackLocationDowner):
                    startOfList=max(index for index, item in enumerate(stackLocationDowner) if item =="_" )
                    childForIsPossibleNotToHaveNonterm=stackLocationDowner[startOfList+1:]
                else:
                    childForIsPossibleNotToHaveNonterm=stackLocationDowner


                stackLocationUpperElem=[]
                findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                if(self.operation=="="):
                    downerBacktrace=Avoid(
                            locationToAvoid=childForIsPossibleNotToHaveNonterm,
                            condition=[{"condition":ExistDiffValInStack(upperStack), "isParentApplicable": True}])
                    prefValUpper={
                    "prefArr":{"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]},
                    "conditions":[{"condition":Not(StackEmpty(upperStack)), "isParentApplicable":True}]
                    }
                    prefChanceUpper1={
                        "prefChance":0.9,
                        "conditions":[]
                    }
                    prefChanceUpper2={
                        "prefChance":1,
                        "conditions":[]
                    }
                    possibleValDowner={
                        "prefArr":{"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]},
                        "conditions":[]
                    }
                    prefValDowner={
                    "prefArr":{"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]},
                    "conditions":[]
                    }
                    prefChanceUpper=[prefChanceUpper1,prefChanceUpper2]
                elif(self.operation=="!="):
                    downerBacktrace=None
                    prefValUpper=None
                    prefChanceUpper=None
                    possibleValDowner={
                        "prefArr":{"values":[],"arrays":[],"notEqualsWithArr":[upperStack]},
                        "conditions":[]
                    }
                    prefValDowner={
                    "prefArr":{"values":[],"arrays":[],"notEqualsWithArr":[upperStack]},
                    "conditions":[]
                    }
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")
                return(
                    [Constraint(
                        var=upperElem,
                        varType=self.getVarType(upperElem),
                        stackLocation=stackLocationUpperElem,
                        structEnd=[RemoveFromStackAsContainingNonterm(stackName=upperStack, nonTermType=self.getVarType(varUpper))] if (type(structuralRelationVariables)==Inside)  else None,
                        trueIndicator=allValuesPrefered),
                    Constraint(
                        var=varUpper,
                        varType=self.getVarType(varUpper),
                        globalInfo=[ VarBool(allValuesPrefered),StackValId(upperStack)],
                        stackLocation=stackLocationUpper,
                        preferedValues=prefValUpper,
                        preferedChanche= prefChanceUpper,
                        operation=AddToStackWithId(upperStack,This(varUpper))),
                    Constraint(
                        var=varDowner,
                        varType=self.getVarType(varDowner),
                        stackLocation=stackLocationDowner,
                        preferedValues=prefValDowner,
                        preferedChanche=prefChanceDowner,
                        possibleValues=possibleValDowner,
                        backtrace=downerBacktrace,
                        operation=Conditional(Not(ExistsInStack(This(varDowner),ToValStack(upperStack))),Assign(allValuesPrefered,False),None))
                    ]
                )
                

        elif(matchVarWithoutStructuralRelation==(forall,exists,True,False,False) or matchVarWithoutStructuralRelation==(forall,exists,False,True,False) or matchVarWithoutStructuralRelation==(forall,exists,False,False,False)):
                upperStack=f"{varUpper}_stack"
                prefArr=None
                equal_val=None
                prefStack=f"{varDowner}_pref_stack"
                varString=None

                #adjust pref/possible
                if(self.operation=="="):
                    if(var1IsString or var2IsString):
                        varString=var1String if var1IsString else var2String
                        prefArr={"values":[varString],"arrays":[], 'notEqualsWithArr':[]}
                        equal_val=String_Token(varString)
                    else:
                        prefArr={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}
                        equal_val=upperStack
                elif(self.operation=="!="):
                    if(var1IsString or var2IsString):
                        varString=var1String if var1IsString else var2String
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}
                        equal_val=String_Token(varString)
                    else:
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}
                        equal_val=upperStack
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")

                additional_global_info= [ValAsStrgStack(prefStack,varString)] if self.operation=="!=" else None

                prefChanceDowner={
                    "prefChance":0.5,
                    "conditions":[]
                }
                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":Not(StackEmpty(upperStack)),"isParentApplicable": True}]
                }

                #adjust condition for remove from stack
                if(not var1IsString and not var2IsString):
                    op=RemoveFromStackWithVal(upperStack,ExistsInStack(This(var=varDowner),upperStack))
                else:
                    op=ParentsRemoveFromStack(condition=Equals(This(var=varDowner),equal_val),stackName=upperStack)


                parentStack=[]
                if(type(structuralRelationVariables) ==Inside):
                    stackLocationUpperElem=[]
                    findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                    until_seen=self.getVarType(upperElem)
                    parentStack=stackLocationUpperElem[:-1]
                elif(type(structuralRelationVariables) ==Before):
                    until_seen="<start>"

                return ([
                    Constraint(var=varUpper, 
                varType=self.getVarType(varUpper), 
                globalInfo=[StackValId(upperStack)], 
                stackLocation=stackLocationUpper, 
                operation=AddToStackWithId(upperStack, This(varUpper)),
                trueIndicator=StackEmpty(upperStack)),

                Constraint(
                    var=varDowner,
                    globalInfo=additional_global_info, 
                    varType=self.getVarType(varDowner),
                    stackLocation=stackLocationDowner, 
                    preferedValues=prefValDowner,  
                    preferedChanche=prefChanceDowner,   
                    backtrace=Seen(valueToSee=prefArr,globalSeenIndicator=ParentExistsInStack(stack=upperStack), until=until_seen,derivationRulesToUse=[],flagForLast=[],parentStack=parentStack), 
                    operation= op)
                ])


    
        elif(matchVar==(forall,exists,False,False,Before,True)):
                stackLocationUpperElem=[]
                findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                
                preStack=f"{varUpper}_stack1"
                useStack=f"{varUpper}_stack2"
                allDownerCorrect=f"all_{varDowner}_correct"
                
                if(self.operation=="="):
                    pref={"values":[],"arrays":[useStack], 'notEqualsWithArr':[]}
                elif(self.operation=="!="):
                    pref={"values":[],"arrays":[], 'notEqualsWithArr':[useStack]}
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")
                
                prefChanceDowner={
                    "prefChance":1,
                    "conditions":[]
                }
                prefValDowner={
                    "prefArr":copy.deepcopy(pref),
                    "conditions":[]
                }
                possibleValDowner={
                    "prefArr":pref,
                    "conditions":[]
                }

                returnArr=[
                    Constraint(var=upperElem,varType=self.getVarType(upperElem),stackLocation=stackLocationUpperElem,
                    globalInfo=[StackValId(preStack),VarBool(allDownerCorrect)],
                    structEnd=[CopyToStackAsParent(preStack,useStack,self.getVarType(varUpper)),RemoveFromStackAsContainingNonterm(preStack,self.getVarType(varUpper))]#childType should be id (von stmt)
                    ),
                    
                    Constraint(var=varUpper,varType=self.getVarType(varUpper),stackLocation=stackLocationUpper,
                    globalInfo=[StackValId(useStack)],
                    operation=AddToStackWithId(preStack, This(varUpper)),trueIndicator=allDownerCorrect
                    ),
                    Constraint(var=varDowner, varType=self.getVarType(varDowner),stackLocation=stackLocationDowner, 
                    preferedValues=prefValDowner,
                    preferedChanche=prefChanceDowner,
                    possibleValues=possibleValDowner,
                    backtrace=Avoid(condition=[{"condition":StackEmpty(useStack), "isParentApplicable": True}], locationToAvoid=stackLocationDowner),
                    operation= 
                    Conditional(condition=Not(StackEmpty(useStack)),ifTrue=Assign(allDownerCorrect, False),ifFalse=None))
                ]
                return(returnArr)
        elif(matchVar==(forall,exists,True,False,Before,True) or matchVar==(forall,exists,False,True,Before,True)):
                upperStack=f"{varUpper}_stack"
                allDownerCorrect=f"all_{varDowner}_correct"
                if((var1IsString and self.var2==varUpper) or (var2IsString and self.var1==varUpper)):

                    requiredStr=var1String if var1IsString else var2String
                    prefVal=None
                    prefValStack=f"{varDowner}_pref_stack"
                    
                    if(self.operation=="="):
                        prefVal={"prefArr":{"values":[requiredStr],"arrays":[], 'notEqualsWithArr':[]},"conditions":[]}
                    elif(self.operation=="!="):
                        if (not((var1IsString and self.var2==varUpper) or (var2IsString and self.var1==varUpper))): raise ValueError("not in the scope")
                        pref={"values":[],"arrays":[], 'notEqualsWithArr':[prefValStack]}
                    else:
                        raise ValueError(f"operation '{self.operation}' not defined")

                    additional_global_info= [ValAsStrgStack(prefValStack,requiredStr)] if self.operation=="!=" else None


                    return [
                        Constraint(var=varUpper,varType=self.getVarType(varUpper),stackLocation=stackLocationUpper,
                        globalInfo=[StackValId(upperStack),VarBool(allDownerCorrect)],
                        preferedValues=prefVal,
                        preferedChanche={"prefChance":0.3,"conditions":[]},
                        operation=Conditional(condition=Equals(This("selection"), String_Token(requiredStr)),ifTrue=AddToStackWithId(upperStack, This(varUpper))),trueIndicator=allDownerCorrect
                        ),
                        Constraint(var=varDowner, varType=self.getVarType(varDowner),stackLocation=stackLocationDowner, 
                        globalInfo=additional_global_info,
                        backtrace=Avoid(condition=[{"condition":StackEmpty(upperStack), "isParentApplicable": True}], locationToAvoid=stackLocationDowner),
                        operation= 
                        Conditional(condition=Not(StackEmpty(upperStack)),ifTrue=Assign(allDownerCorrect, False),ifFalse=None))
                    ]
                else:
                    raise ValueError("not valid")
                    
        elif(firstQuantor,secondQuantor,type(structuralRelationVariables),yIsInsideX)==(forall,exists,Inside,True):
                upperStack=f"{varUpper}_stack"

                pref=None
                prefStack=f"{varDowner}_pref_stack"
                varString=None

                if(self.operation=="="):
                    if(var1IsString or var2IsString):
                        varString=var1String if var1IsString else var2String
                        pref={"values":[varString],"arrays":[], 'notEqualsWithArr':[]}
                    else:
                        pref={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}

                elif(self.operation=="!="):#nur pref/possible werte ändern
                    if(var1IsString or var2IsString):
                        varString=var1String if var1IsString else var2String
                        pref={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}
                    else:
                        pref={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")
                
                additional_global_info= [ValAsStrgStack(prefStack,varString)] if self.operation=="!=" else None
                
                allDownerCorrect=f"all_{varDowner}_correct"
                prefChanceDowner={
                    "prefChance":1,
                    "conditions":[]
                }
                prefValDowner={
                    "prefArr":copy.deepcopy(pref),
                    "conditions":[]
                }
                possibleValDowner={
                    "prefArr":pref,
                    "conditions":[]
                }
                if(self.spezification!=None):
                    upperElem=self.elemName
                    stackLocationUpperElem=[]
                    findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                    return([
                        Constraint(var=upperElem,varType=self.getVarType(upperElem),stackLocation=stackLocationUpperElem,
                        structEnd= [RemoveFromStackAsContainingNonterm(stackName=upperStack, nonTermType=self.getVarType(varUpper))],trueIndicator=allDownerCorrect
                        ),
                        Constraint(var=varUpper,varType=self.getVarType(varUpper),stackLocation=stackLocationUpper,
                        globalInfo=[StackValId(upperStack),VarBool(allDownerCorrect)],
                        operation=AddToStackWithId(upperStack, This(varUpper)),
                        ),

                        Constraint(var=varDowner, varType=self.getVarType(varDowner),stackLocation=stackLocationDowner, 
                        preferedValues=prefValDowner,
                        globalInfo=additional_global_info, 
                        preferedChanche=prefChanceDowner,
                        possibleValues=possibleValDowner,
                        backtrace=Avoid(condition=[{"condition":StackEmpty(upperStack), "isParentApplicable": True}], locationToAvoid=stackLocationDowner),
                        operation= 
                        Conditional(condition=Not(StackEmpty(upperStack)),ifTrue=Assign(allDownerCorrect, False),ifFalse=None))
                    ])
                else:
                    raise ValueError("constraint can not be translated")
                    

        elif(matchVarWithoutStructuralRelation==(exists,forall,False,True,False) or matchVarWithoutStructuralRelation==(exists,forall,True,False,False) or matchVarWithoutStructuralRelation==(exists,forall,False,False,False)):
                varString=var1String if var1IsString else var2String

                upperStack=f"{varUpper}_stack"
                upperIdStack=f"{varUpper}_stackId"
                lastUpper=f"last_{varUpper}"
                downerInUpperSeen=f"{varDowner}_in_{varUpper}_seen"
                trueIndicator=IsTrue(downerInUpperSeen)
                prefArr=None
                conditionVal=None
                prefStack=f"{varDowner}_pref_stack"
                additional_global_info= [ValAsStrgStack(prefStack,varString)] if self.operation=="!=" and (var1IsString or var2IsString) else []

                prefChanceDowner={
                    "prefChance":1,
                    "conditions":[{"condition":IsTrue(lastUpper), "isParentApplicable":True}]
                }

                if(self.operation=="="):
                    if(var1IsString or var2IsString):
                        prefArr={"values":[varString],"arrays":[], 'notEqualsWithArr':[]}              
                        conditionVal=Not(Equals(This(varDowner),String_Token(varString)))
                    else:
                        prefArr={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}              
                        conditionVal=Not(ExistsInStack(This(varDowner),upperStack))
                elif(self.operation=="!="):
                    if(var1IsString or var2IsString):
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}               
                        conditionVal=Equals(This(varDowner),prefStack)
                    else:
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}               
                        conditionVal=ExistsInStack(This(varDowner),upperStack)
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")

                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True}]
                }
                
                if(type(structuralRelationVariables)==Inside):
                    additional_global_info.append(VarBool(downerInUpperSeen))
                    if(self.upperQuantorExpression.spezification!=None):
                        stackLocationUpperElem=[]
                        findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                    
                        childFoundName=f"help_{varDowner}_in_{varUpper}_seen"

                        return([
                            Constraint(
                        var=upperElem,
                        varType=self.getVarType(upperElem),
                        stackLocation=stackLocationUpperElem,
                        structEnd=[
                            SearchInParentNonterm(childType=self.getVarType(varUpper),stackName=upperStack,indicesFoundArrName=childFoundName),
                            Conditional(
                                condition=Not(StackEmpty(childFoundName)), 
                                ifTrue=Assign(downerInUpperSeen,True),
                                ifFalse=None)],
                        trueIndicator=trueIndicator),

                            Constraint(var=varUpper, 
                        varType=self.getVarType(varUpper), 
                        globalInfo=[StackValId(upperStack),VarBool(lastUpper)], 
                        stackLocation=stackLocationUpper, 
                        backtrace=NontermSeen(globalSeenIndicator=IsTrue(downerInUpperSeen), until="<start>",derivationRulesToUse=stackLocationUpper,flagForLast=lastUpper,notSeenCondition=And(IsFalse(downerInUpperSeen),StackEmpty(upperStack))),
                        operation=Conditional(condition=IsFalse(downerInUpperSeen),ifTrue=AddToStackWithId(upperStack, This(varUpper)),ifFalse=None)),

                        Constraint(var=varDowner, varType=self.getVarType(varDowner),
                        globalInfo=additional_global_info,
                        stackLocation=stackLocationDowner, preferedValues=prefValDowner,
                        preferedChanche=prefChanceDowner,
                        operation= Conditional(condition=IsFalse(downerInUpperSeen),ifTrue=ParentsRemoveFromStack(stackName=upperStack, condition=conditionVal),ifFalse=None))
                        ])
                    else:
                        return([Constraint(
                        var=varUpper, 
                        varType=self.getVarType(varUpper), 
                        globalInfo=[StackValId(upperStack),VarBool(lastUpper)], 
                        stackLocation=stackLocationUpper, 
                        backtrace=NontermSeen(globalSeenIndicator=IsTrue(downerInUpperSeen), until="<start>",derivationRulesToUse=stackLocationUpper,flagForLast=lastUpper,notSeenCondition=And(IsFalse(downerInUpperSeen),StackEmpty(upperStack))),
                        operation=Conditional(condition=IsFalse(downerInUpperSeen),ifTrue=AddToStackWithId(upperStack, This(varUpper)),ifFalse=None),
                        structEnd= [Conditional(condition=ExistsInStack(var=upperIdStack,stackName=ToValStack(upperStack)), ifTrue=Assign(downerInUpperSeen,True),ifFalse=None)],
                        trueIndicator=trueIndicator),

                        Constraint(
                        var=varDowner, 
                        varType=self.getVarType(varDowner),
                        globalInfo=additional_global_info,
                        stackLocation=stackLocationDowner, 
                        preferedValues=prefValDowner,
                        preferedChanche=prefChanceDowner,   
                        operation= Conditional(condition=IsFalse(downerInUpperSeen),ifTrue=RemoveFromStackWithVal(stackName=upperStack, condition=conditionVal),ifFalse=None))
                        ])
                elif(type(structuralRelationVariables)==Before):
                    return([Constraint(
                        var=varUpper, 
                        varType=self.getVarType(varUpper), 
                        globalInfo=[StackValId(upperStack),VarBool(lastUpper)], 
                        stackLocation=stackLocationUpper, 
                        backtrace=NontermSeen(globalSeenIndicator=Not(StackEmpty(upperStack)), until="<start>",derivationRulesToUse=stackLocationUpper,flagForLast=lastUpper,notSeenCondition=StackEmpty(upperStack)),
                        operation=AddToStackWithId(upperStack, This(varUpper)),
                        trueIndicator=trueIndicator),
                        Constraint(
                        var=varDowner, 
                        varType=self.getVarType(varDowner),
                        globalInfo=additional_global_info,
                        stackLocation=stackLocationDowner, 
                        preferedValues=prefValDowner,
                        preferedChanche=prefChanceDowner,   
                        operation= RemoveFromStackWithVal(stackName=upperStack, condition=conditionVal))
                        ])
                else:
                    raise ValueError("structuralRelation unknown")
        
        
        elif(firstQuantor,secondQuantor,type(structuralRelationVariables),yIsInsideX)==(exists,forall,Before,True):
                upperSeen=f"{varDowner}_in_{varUpper}_seen"
                lastUpper=f"last_{varUpper}"
                upperStack=f"{varUpper}_stack"
                trueIndicator=IsTrue(upperSeen)
                varString=var1String if var1IsString else var2String
                prefArr=None
                prefStack=f"{varDowner}_pref_stack"
                additional_global_info=[]

                

                equal_val=None


                if(self.operation=="="):
                    if(var1IsString or var2IsString):
                        prefArr={"values":[varString],"arrays":[], 'notEqualsWithArr':[]}
                    else:
                        prefArr={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}
                        additional_global_info.append(StackValId(upperStack))
                elif(self.operation=="!="):
                    if(var1IsString or var2IsString):
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}
                        additional_global_info.append(ValAsStrgStack(prefStack,varString))
                    else:
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}
                        additional_global_info.append(StackValId(upperStack))

                else:
                    raise ValueError(f"operation '{self.operation}' not defined")

                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":IsFalse(upperSeen), "isParentApplicable":True}]
                    }
                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":IsFalse(upperSeen), "isParentApplicable":True}]
                    }
                prefChanceDowner={
                        "prefChance":0.8,
                        "conditions":[]
                    }
        

                op=[]
                eq=None
                if(var1IsString or var2IsString):
                    eq=Equals(This("selection"),varString)
                    if(self.operation=="!="):
                        eq=Not(eq)
                op.append(Conditional(eq, Assign(upperSeen, True)))


                if (((var1IsString and self.var2==varUpper) or (var2IsString and self.var1==varUpper))):
                    return([
                        Constraint(
                            var=varUpper, 
                            varType=self.getVarType(varUpper),
                            globalInfo=[VarBool(upperSeen),VarBool(lastUpper)],
                            operation=op,
                            backtrace=Seen(IsFalse(upperSeen),until="<start>",derivationRulesToUse=stackLocationDowner,flagForLast=lastUpper,valueToSee=prefArr,doWithLastValue=None),
                            stackLocation=stackLocationDowner, 
                            preferedValues=prefValDowner,
                            preferedChanche=prefChanceDowner,
                            trueIndicator=trueIndicator),
                        Constraint(
                            var=varDowner, 
                            globalInfo=additional_global_info,
                            varType=self.getVarType(varDowner),
                            operation=[Assign(upperSeen, False), AddToStackWithId(upperStack,This())],
                            backtrace=Avoid(locationToAvoid=self.getVarType(varDowner), condition=[{"condition":And(IsFalse(upperSeen),IsTrue(lastUpper)), "isParentApplicable": True}]),)  
                    ])
                else:


                    prefValDowner={
                        "prefArr":prefArr,
                        "conditions":[{"condition":IsFalse(upperSeen), "isParentApplicable":True}]
                        }

                    prefChanceDowner={
                            "prefChance":1,
                            "conditions":[]
                        }

                    possibleValDowner={
                            "prefArr":prefArr,
                            "conditions":[{"condition":IsFalse(upperSeen), "isParentApplicable":True}]
                            }

                    return([    
                        Constraint(
                            var=varUpper, 
                            varType=self.getVarType(varUpper),
                            globalInfo=[VarBool(upperSeen),VarBool(lastUpper)],
                            operation=[Assign(upperSeen, True)],
                            backtrace=NontermSeen(globalSeenIndicator=IsFalse(upperSeen), until="<start>",derivationRulesToUse=stackLocationUpper,flagForLast=lastUpper,notSeenCondition=IsFalse(upperSeen)),
                            stackLocation=stackLocationDowner),  
                        Constraint(
                            var=varDowner, 
                            globalInfo=additional_global_info,
                            operation=op,
                            varType=self.getVarType(varDowner),
                            possibleValues=possibleValDowner,
                            preferedValues=prefValDowner,
                            preferedChanche=prefChanceDowner,
                            backtrace=Avoid(locationToAvoid=self.getVarType(varDowner),condition=[{"condition":And(IsFalse(upperSeen),IsTrue(lastUpper)), "isParentApplicable": True}]))])
        
        elif(firstQuantor,secondQuantor,type(structuralRelationVariables),yIsInsideX)==(exists,forall,Inside,True):
                stringVal=var1String if var1IsString else var2String           
                downerInUpperSeen=f"{varDowner}_in_{varUpper}_seen"
                upperStack=f"{varUpper}_stack"
                firstIsClosed=f"first_{varUpper}_closed"
                upperExists=f"{varUpper}_exists"
                prefStack=f"{varDowner}_pref_stack"

                trueIndicator=downerInUpperSeen
                constr=None
                additional_global_info=[]

                if(self.operation=="="):
                    if(var1IsString or var2String):
                        prefArr={"values":[stringVal],"arrays":[], 'notEqualsWithArr':[]}
                        constr=Equals(This("selection"),String_Token(stringVal))
                    else:
                        prefArr={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}
                        constr= ForallValInStack(condition=Equals(This("selection"),String_Token(f"{upperStack}[i]")) ,stack=upperStack, ifTrue=Assign(downerInUpperSeen,True),ifFalse=None)
                        additional_global_info.append([StackValId(upperStack)])
                elif(self.operation=="!="):
                    if(var1IsString or var2String):
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}
                        additional_global_info.append(ValAsStrgStack(prefStack,varString))
                        constr=Not(Equals(This("selection"),String_Token(stringVal)))
                    else:
                        prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}
                        constr= ForallValInStack(condition=Not(Equals(This("selection"),String_Token(f"{upperStack}[i]"))) ,stack=upperStack, ifTrue=Assign(downerInUpperSeen,True),ifFalse=None)
                        additional_global_info.append([StackValId(upperStack)])
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")


                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":And(Not(downerInUpperSeen),Not(firstIsClosed)), "isParentApplicable":True}]
                }
                prefChanceDowner={
                    "prefChance":0.3,
                    "conditions":[{"condition":And(Not(downerInUpperSeen),Not(firstIsClosed)), "isParentApplicable":True}]
                }

                if(upperElem!=None):
                    stackLocationUpperElem=[]
                    findPathToVar(structuralConstraints,lexer, stackLocationUpperElem, self, upperElem, grammar)
                    return([

                    Constraint(
                            var=upperElem, 
                            varType=self.getVarType(upperElem), 
                            globalInfo=[VarBool(firstIsClosed),VarBool(upperExists)], 
                            stackLocation=stackLocationUpperElem, 
                            structEnd=[Assign(firstIsClosed, True)]
                    ),
                    Constraint(
                            var=varUpper, 
                            varType=self.getVarType(varUpper), 
                            globalInfo=additional_global_info,
                            stackLocation=stackLocationUpper, 
                            operation=[ Assign(downerInUpperSeen, False),Assign(upperExists, True)],
                            trueIndicator=trueIndicator,
                            backtrace=Avoid(locationToAvoid=stackLocationUpper,condition=[{"condition":IsTrue(firstIsClosed), "isParentApplicable": True}]),
                    ),

                    Constraint(
                        var=varDowner, 
                        varType=self.getVarType(varDowner),
                        globalInfo=[VarBool(downerInUpperSeen)],
                        stackLocation=stackLocationDowner, 
                        preferedValues=prefValDowner,
                        preferedChanche=prefChanceDowner,
                        operation=[Conditional(condition=Or(constr,IsFalse(upperExists)), ifTrue=Assign(downerInUpperSeen, True))],
                        backtrace=Seen(IsFalse(downerInUpperSeen),until=self.getVarType(varUpper),derivationRulesToUse=stackLocationDowner,flagForLast=None,valueToSee=prefArr,doWithLastValue=None,parentStack=stackLocationUpper[:-1])
                    )  
                    ])
                else:
                    if(var1IsString or var2String): 
                        raise ValueError("not supported")
                    else:
                        return([
                            Constraint(
                                var=varUpper, 
                                varType=self.getVarType(varUpper), 
                                globalInfo=additional_global_info,
                                stackLocation=stackLocationUpper, 
                                operation=[ Assign(downerInUpperSeen, False),Assign(upperExists, True)],
                                trueIndicator=trueIndicator,
                                backtrace=Avoid(locationToAvoid=stackLocationUpper,condition=[{"condition":IsTrue(firstIsClosed), "isParentApplicable": True}]),
                                structEnd=[Assign(firstIsClosed, True)]
                            ),
                        
                            Constraint(
                                var=varDowner, 
                                varType=self.getVarType(varDowner),
                                globalInfo=[VarBool(downerInUpperSeen),VarBool(firstIsClosed),VarBool(upperExists)],
                                stackLocation=stackLocationDowner, 
                                preferedValues=prefValDowner,
                                preferedChanche=prefChanceDowner,
                                operation=[Conditional(condition=Or(constr,IsFalse(upperExists)), ifTrue=Assign(downerInUpperSeen, True))],
                                backtrace=Seen(IsFalse(downerInUpperSeen),until=self.getVarType(varUpper),derivationRulesToUse=stackLocationDowner,flagForLast=None,valueToSee=prefArr,doWithLastValue=None,parentStack=stackLocationUpper[:-1])
                            )  ])

        elif(matchVarWithoutStructuralRelation==(exists,exists,False,True,True) or matchVarWithoutStructuralRelation==(exists,exists,False,True,False) or matchVarWithoutStructuralRelation==(exists,exists,True,False,True) or matchVarWithoutStructuralRelation==(exists,exists,True,False,False) ):
                downerInUpperSeen=f"{varDowner}_in_{varUpper}_seen"
                lastUpper=f"last_{varUpper}"
                lastDowner=f"last_{varDowner}"
                upperStack=f"{varUpper}_stack"
                trueIndicator=IsTrue(downerInUpperSeen)
                varString=var1String if var1IsString else var2String
                prefArr=None
                prefStack=f"{varDowner}_pref_stack"
                additional_global_info= [VarBool(lastUpper),ValAsStrgStack(prefStack,varString)] if self.operation=="!=" else [VarBool(lastUpper)]


                if(self.operation=="="):
                    prefArr={"values":[varString],"arrays":[], 'notEqualsWithArr':[]}
                elif(self.operation=="!="):
                    prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]}
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")

                prefValDowner={
                    "prefArr":prefArr,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True}]
                }
                prefChanceDowner1={
                    "prefChance":1,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True},
                    {"condition":IsTrue(lastUpper),"isParentApplicable":True},
                    {"condition":IsTrue(lastDowner),"isParentApplicable":True}]
                }
                prefChanceDowner2={
                    "prefChance":0.3,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True}]
                }

                untilVal=None
                parentStack=[]
                if(type(structuralRelationVariables)==Inside):
                    untilVal=self.getVarType(varUpper)
                    parentStack=stackLocationUpper[:-1]
                elif(type(structuralRelationVariables)==Before):
                    untilVal="<start>"
                else:
                    raise ValueError("structuralRelation unknown")
                    
                return([Constraint(
                    var=varUpper, 
                    varType=self.getVarType(varUpper),  
                    globalInfo=additional_global_info,
                    stackLocation=stackLocationUpper,
                    backtrace= NontermSeen(globalSeenIndicator=IsTrue(downerInUpperSeen), until="<start>", flagForLast=lastUpper,derivationRulesToUse=stackLocationUpper,notSeenCondition=IsFalse(downerInUpperSeen)),
                    trueIndicator=trueIndicator
                ),
                    Constraint(
                        var=varDowner, 
                        varType=self.getVarType(varDowner), 
                        globalInfo=[VarBool(downerInUpperSeen),
                        VarBool(lastDowner)],
                        stackLocation=stackLocationDowner,
                        preferedValues= prefValDowner,
                        preferedChanche=[prefChanceDowner1,prefChanceDowner2],
                        backtrace=Seen(valueToSee=prefArr,
                            globalSeenIndicator=And(IsFalse(downerInUpperSeen),IsTrue(lastUpper)), until=untilVal, doWithLastValue=Assign(lastDowner, True),
                            derivationRulesToUse=stackLocationDowner,
                            flagForLast=None,parentStack=parentStack),
                        operation=Conditional(condition=Equals(This(varDowner),String_Token(varString)),ifTrue=Assign(downerInUpperSeen, True),ifFalse=None))
                    ])      
        elif(matchVarWithoutStructuralRelation==(exists,exists,False,False,True) or matchVarWithoutStructuralRelation==(exists,exists,False,False,False)):
                
                downerInUpperSeen=f"{varDowner}_in_{varUpper}_seen"
                lastUpper=f"last_{varUpper}"
                lastDowner=f"last_{varDowner}"
                upperStack=f"{varUpper}_stack"
                trueIndicator=IsTrue(downerInUpperSeen)                
                operationDowner=[Conditional(condition=ExistsInStack(var=This(varDowner),stackName=ToValStack(upperStack)),ifTrue=Assign(downerInUpperSeen, True),ifFalse=None)]
                operationUpper=[AddToStackWithId(upperStack,This(varUpper))]

                downerInUpperSeen=f"{varDowner}_in_{varUpper}_seen"
                lastUpper=f"last_{varUpper}"
                lastDowner=f"last_{varDowner}"
                trueIndicator=IsTrue(downerInUpperSeen)
                if(self.operation=="="):
                    prefArr={"values":[],"arrays":[upperStack], 'notEqualsWithArr':[]}
                elif(self.operation=="!="):
                    prefArr={"values":[],"arrays":[], 'notEqualsWithArr':[upperStack]}
                else:
                    raise ValueError(f"operation '{self.operation}' not defined")
                prefValDowner={
                "prefArr":prefArr,
                "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True}]
                }
                prefChanceDowner1={
                    "prefChance":1,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True},{"condition":IsTrue(lastUpper),"isParentApplicable":True},{"condition":IsTrue(lastDowner),"isParentApplicable":True}]
                }
                prefChanceDowner2={
                    "prefChance":0.3,
                    "conditions":[{"condition":IsFalse(downerInUpperSeen), "isParentApplicable":True}]
                }


                untilVal=None
                parentStack=[]
                if(type(structuralRelationVariables)==Inside):
                    untilVal=self.getVarType(varUpper)
                    parentStack=stackLocationUpper[:-1]
                elif(type(structuralRelationVariables)==Before):
                    untilVal="<start>"
            
                return([Constraint(
                    var=varUpper, 
                    varType=self.getVarType(varUpper),  
                    globalInfo=[VarBool(lastUpper),StackValId(upperStack)],
                    stackLocation=stackLocationUpper,
                    backtrace= NontermSeen(globalSeenIndicator=IsTrue(downerInUpperSeen), until="<start>", flagForLast=lastUpper,derivationRulesToUse=stackLocationUpper,notSeenCondition=IsFalse(downerInUpperSeen)),
                    trueIndicator=trueIndicator,
                    operation=operationUpper
                    ),
                    Constraint(
                        var=varDowner, 
                        varType=self.getVarType(varDowner), 
                        globalInfo=[VarBool(downerInUpperSeen),
                        VarBool(lastDowner)],
                        stackLocation=stackLocationDowner,
                        preferedValues= prefValDowner,
                        preferedChanche=[prefChanceDowner1,prefChanceDowner2],
                        backtrace=Seen(valueToSee=prefArr,
                            globalSeenIndicator=And(IsFalse(downerInUpperSeen),IsTrue(lastUpper)), until=untilVal, doWithLastValue=Assign(lastDowner, True),
                            derivationRulesToUse=stackLocationDowner,
                            flagForLast=None,parentStack=parentStack ),
                        operation=operationDowner)
                    ])
               















    def getVarOnWay(self):
        var1IsString=re.match('"(.*)"',self.var1)
        var2IsString=re.match('"(.*)"',self.var2)

        varOnWay2=[]
        varOnWay1=[]
        if(not var1IsString):
            self.getVariablesOnWay(self.var1,varOnWay1)
            varOnWay1 = varOnWay1[::-1]
        if(not var2IsString):
            self.getVariablesOnWay(self.var2,varOnWay2)
            varOnWay2 = varOnWay2[::-1]
        return(varOnWay1,varOnWay2)

    def getFullQuantorExpression(self, grammar, lexer):
        structuralConstraints=[]
        self.findAllStructuralConstraints(structuralConstraints)
        basisConstraint=self.makeBasisConstraint(grammar,lexer, structuralConstraints)[::-1]
        return basisConstraint
        
    def  handleBacktrace(self,fullQuantorExpression, grammar, lexer):
        for constraint in fullQuantorExpression:
            
            
            if(constraint.backtrace):
                backtraceType=type(constraint.backtrace)
                waysToGo=[]
                connectionArr=[]
                recursionArr=[]
                arr=[]
                if(backtraceType==Seen):
                    trueIndicator=constraint.backtrace.globalSeenIndicator
                    parent=constraint.backtrace.until
                    child=constraint.varType
                    prefForRealLast=constraint.backtrace.valueToSee
                    connectionArr=constraint.backtrace.parentStack

                    getSeenInfo(lexer, waysToGo,connectionArr,recursionArr, arr, parent, child, grammar,[False],prefForRealLast,trueIndicator)
                    

                elif (backtraceType==NontermSeen):
                    parent=constraint.backtrace.until
                    childStackLocation=constraint.backtrace.derivationRulesToUse
                    notSeenCondition=constraint.backtrace.notSeenCondition
                    flagForLast=constraint.backtrace.flagForLast
       
                    getSeenInfo(lexer, waysToGo,connectionArr,recursionArr, arr, parent, childStackLocation[0], grammar,[False],None,notSeenCondition, flagToSetInRealLast=flagForLast)

                elif (backtraceType==Avoid):
                    
                    condition=constraint.backtrace.condition

                    if(type(condition) != list):
                        condition=[condition]

                    self.getAvoidInfo(fullQuantorExpression, grammar, constraint.backtrace.locationToAvoid,condition, lexer)
                    fullQuantorExpression[-1].printAttributesAsString()

                else:
                    raise ValueError("backtrace type not yet implemented")
            
                for constraint in waysToGo:
                    fullQuantorExpression.append(constraint)



    def getAvoidInfo(self,constraints, grammar, pathToVar,conditionArr, lexer, startVar="<start>", fixedStartVar=False):
        reachableNonterms=[startVar]
        getReachableNonterms(reachableNonterms, startVar, grammar)
        currArrIndex=len(pathToVar)-2 
        while(currArrIndex>=0):
            lastSpez=pathToVar[currArrIndex]
            if(isSpezRule(lastSpez)):
                devRuleToAvoid=lastSpez[1:-1]
                currNonterm=pathToVar[currArrIndex-1]
                allDevRules=grammar[currNonterm]
                devRuleToKeep=[x for x in allDevRules if x != devRuleToAvoid]
                if(bool(devRuleToKeep)):
                    varName=GlobalDefines.normalize('avoidInfo', GlobalDefines.ISLA_RULE)
                    indicator=f"{varName}_indicator"
                    checkArrName=f"{varName}_checkArr"
  
                    checkArr=set()
                    if(expressionStartsWithNonterminal(devRuleToAvoid)):
                        firstNonterm=findFirstNonTerminal(devRuleToAvoid)
                        allDevRulesFirstNonterm=grammar[firstNonterm]
                        if(GlobalDefines.EPSILON in allDevRulesFirstNonterm):
                            follow=createFollowTable(firstNonterm, grammar, dict())
                            checkArr.update(set(follow))
                        checkArr.update(createFirstTableForExp(firstNonterm,grammar))
                    else:
                        checkArr.add(findFirstTerminal(devRuleToAvoid))



                    
                    prefStack=f"{varName}_pref_stack"
                    currPathToVar=pathToVar[:currArrIndex].copy()
                    prefVal={
                        "prefArr": {"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]},
                        "conditions":conditionArr
                    }
                    prefChance={
                        "prefChance":1,
                        "conditions":conditionArr
                    }
                    possibleVal={
                        "prefArr": {"values":[],"arrays":[], 'notEqualsWithArr':[prefStack]},
                        "conditions":conditionArr
                    }
                    constraints.append(Constraint(
                    var=varName,
                    varType=pathToVar[currArrIndex-1],
                    stackLocation=currPathToVar,
                    preferedValues=prefVal,
                    preferedChanche=prefChance,
                    possibleValues=possibleVal,
                    globalInfo=[VarBool(indicator),CreatePrefPossibleArray(prefStack,ArrToStack(checkArr))],
                    operation=SequentialExecution(CreatePrefPossibleArray(checkArrName,ArrToStack(checkArr)),Conditional(ExistsInStack(This("select"),ToValStack(checkArrName)),Assign(indicator,True),None)),
                    trueIndicator=indicator
                    ))
                    return
            elif lastSpez[0]=="$":
                #proof with recursion
                self.getAvoidInfo(constraints, grammar, pathToVar[:-1],conditionArr, lexer, startVar, fixedStartVar)
                #skip recursion
                currArrIndex-=int(lastSpez[1:])
            elif lastSpez=="_":
                if(pathToVar[currArrIndex+1][0]!="("):
                    reachableNonterms2=[pathToVar[currArrIndex+1]]
                    getReachableNonterms(reachableNonterms, pathToVar[currArrIndex+1], grammar)
                    self.avoidForLastPositionInStacklocation(constraints, pathToVar[currArrIndex+1], grammar, conditionArr,[],pathToVar[:currArrIndex] ,reachableNonterms2)
                    return
            else:
                raise ValueError(f"string '{lastSpez}' not expected in avoidInfo")
            currArrIndex-=2
        valueToAvoid=pathToVar[0] 
        self.avoidForLastPositionInStacklocation(constraints, valueToAvoid, grammar, conditionArr,startVar, [], [],reachableNonterms)



    def avoidForLastPositionInStacklocation(self,constraints, valueToAvoid, grammar,conditionArr,startVar,avoidedNonterms, additionalPathToVar, allowedNonterms ):
        avoidedNonterms.append(valueToAvoid)
        devRulesWithAvoidCounter=0
        derivationRules=grammar[startVar]
        for devRule in derivationRules:
            if(valueToAvoid in devRule):
                devRulesWithAvoidCounter+=1
        
        if(devRulesWithAvoidCounter==len(derivationRules)):
            if(len(additionalPathToVar)>0):
                if(not additionalPathToVar[-1] in avoidedNonterms):
                    newAdditionalPathToVar=additionalPathToVar[:-1]
                    self.avoidForLastPositionInStacklocation(constraints, startVar, grammar,conditionArr,newAdditionalPathToVar[-1], avoidedNonterms,newAdditionalPathToVar,allowedNonterms)
            else:
                nontermsThatContainStartVar=self.getNontermsThatContainSpezificNonterm(self, grammar, startVar)
                for newStartVar in nontermsThatContainStartVar:
                    if(not (newStartVar in avoidedNonterms) and newStartVar in allowedNonterms):
                        self.avoidForLastPositionInStacklocation(constraints, startVar, grammar,conditionArr,newStartVar,  avoidedNonterms,[newStartVar],allowedNonterms)
        else:
            
            if(devRulesWithAvoidCounter==0):
                for devRule in derivationRules:
                        
                    currNonterms=findAllNonTerminal(devRule)
                    for newStartVar in currNonterms:
                        if(not newStartVar in avoidedNonterms):
                            if(len(additionalPathToVar)>0):
                                newAdditionalPathToVar=additionalPathToVar+["_",newStartVar ]
                            else:
                                newAdditionalPathToVar=[newStartVar]
                            avoidedNonterms.append(newStartVar)
                            self.avoidForLastPositionInStacklocation(constraints, valueToAvoid, grammar,conditionArr,newStartVar,avoidedNonterms, newAdditionalPathToVar ,allowedNonterms)
    
                    
            if(devRulesWithAvoidCounter>0):
                checkArr=[]
                for devRule in derivationRules:
                    if(not valueToAvoid in devRule):
                        if(expressionStartsWithNonterminal(devRule)):
                            checkArr.extend(createFirstTableForExp(devRule, grammar))
                        elif(derivationOptionIsEpsylon(devRule)):
                            valsToAppend=createFollow_dict(grammar)[startVar]
                            checkArr.extend(list(valsToAppend))
                        else:
                            checkArr.append(findFirstTerminal(devRule))
                varName=GlobalDefines.normalize('avoidInfo', GlobalDefines.ISLA_RULE)
                indicator=f"{varName}_indicator"
                checkArrName=f"{varName}_checkArr"
                prefVal={
                    "prefArr": {"values":checkArr,"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":conditionArr
                }
                prefChance={
                    "prefChance":1,
                    "conditions":conditionArr
                }
                possibleVal={
                    "prefArr":  {"values":checkArr,"arrays":[], 'notEqualsWithArr':[]},
                    "conditions":conditionArr
                }
                constraints.append(Constraint(
                var=varName,
                varType=startVar,
                stackLocation=additionalPathToVar,
                preferedValues=prefVal,
                preferedChanche=prefChance,
                possibleValues=possibleVal,
                globalInfo=[VarBool(indicator)],
                operation=SequentialExecution(CreatePrefPossibleArray(checkArrName,ArrToStack(checkArr)),Conditional(ExistsInStack(This("select"),ToValStack(checkArrName)),Assign(indicator,True),None)),
                trueIndicator=indicator
                ))
                 
    def getNontermsThatContainSpezificNonterm(self, grammar, nonterm):
        nontermList=[]
        for parent, spez in grammar.items():
            if( nonterm in spez):
                nontermList.append(parent)
        return nontermList
                        
                    
    
    def libForm_quantorExpression_forConstraint(self,constraint, libForm_quantorExpression, grammar):
        #handle Stack location
            if((libForm_quantorExpression.get(constraint.varType) is None) ):
                libForm_quantorExpression[constraint.varType]={}




            stackLocation=StackLocationArr(constraint.var,constraint.stackLocation)
            stackLocationString=stackLocation.generateStackLocationIsValidString()

            if(not "stackLocation" in libForm_quantorExpression[constraint.varType]):
                libForm_quantorExpression[constraint.varType]["stackLocation"]=""
            libForm_quantorExpression[constraint.varType]["stackLocation"]+=stackLocationString

            stackLocationConditionToken=stackLocation.generateStackLocationConditionToken()

            #handle structBegin

            if(not "structBegin" in libForm_quantorExpression[constraint.varType]):
                libForm_quantorExpression[constraint.varType]["structBegin"]=""
            if(constraint.structBegin):
                sequentialExec=None
                for i in constraint.structBegin:
                    sequentialExec=SequentialExecution(sequentialExec,i) 
                libForm_quantorExpression[constraint.varType]["structBegin"]+=Conditional(stackLocationConditionToken,sequentialExec).__str__()
                
            #handle structEnd
            if(not "structEnd" in libForm_quantorExpression[constraint.varType]):
                libForm_quantorExpression[constraint.varType]["structEnd"]=""
            if(constraint.structEnd):
                sequentialExec=None
                for i in constraint.structEnd:
                    sequentialExec=SequentialExecution(sequentialExec,i) 
                libForm_quantorExpression[constraint.varType]["structEnd"]+=Conditional(stackLocationConditionToken,sequentialExec).__str__()


            #handle operation
            if(not "operation" in libForm_quantorExpression[constraint.varType]):
                libForm_quantorExpression[constraint.varType]["operation"]=""
            if(constraint.operation):
                sequentialExec=None
                if(type(constraint.operation)==type([])):
                    for i in constraint.operation:
                        sequentialExec=SequentialExecution(sequentialExec,i) 
                else:
                    sequentialExec=constraint.operation
                libForm_quantorExpression[constraint.varType]["operation"]+=Conditional(stackLocationConditionToken,sequentialExec).__str__()


            #handle globalInfo
            if(constraint.globalInfo):
                for item in constraint.globalInfo :
                    libForm_quantorExpression["globalInfo"].append(item.__str__())


            


    def generateConstraintConditionToken(self, stackLocArr,conditions):
        commonConditions=None
        locations=stackLocArr.generateStackLocationConditionToken()
        
        #add all conditions that must apply
        for condition in conditions:
            commonConditions=And(commonConditions, condition["condition"])
        
        return And(locations,commonConditions)
        

    def generateConditionString(self, conditionsArr):
        conditionString=""
        for conditionInfo in conditionsArr:
            condition=conditionInfo["condition"].__str__()
            conditionString+= f" && {condition}"
        return conditionString


        
    def getLibForm_Expression(self,fullQuantorExpression:List[Constraint],grammar)-> Dict[str,Dict[str, List[str]]]:
        
        findSpecificPosition="""

    //_____________isSpecificPosition_BEGIN_________________

//returns index of common list
char addListInt(int list1[],int list1Index, int mergedList[], int mergedListIndex){
    local int i;
    for(i=0;i<=list1Index;i++){
        mergedList+=list1[i];
    }
    return list1Index + mergedListIndex + 1;
}



int handleRecursion(string positionToProof [],int arrLen, int currStackCount){
//int handleRecursion(string positionToProof [],int arrLen, int currStackCount, int checkContinueArr []){
    local int recursionCount=0;
    local int recursionBegins[0];
    local int recursionLenArr[0];

    //___get all possible recursions
    local int currArrIndex=arrLen-1;
    while(currArrIndex>=0 && positionToProof[currArrIndex][0]=='$'){//while new recursion 
        recursionCount=recursionCount+1;
        local int help=currArrIndex;
        recursionBegins+=help;
        local string s2= SubStr( positionToProof[currArrIndex], 1 );
        //_add new recursion end as integer to array
        local int currRecLen=Atoi(s2);
        recursionLenArr+=currRecLen;

        currArrIndex=help-1 - currRecLen;

    }

        ////___try to parse ohne recursion
        //local byte isSpezPosWithoutRec=isSpecificPosition( positionToProof, currArrIndex+1, currArrIndex+1, currStackCount);
        //if(isSpezPosWithoutRec){
        //    return True;
        //}//bei else soll es einfach weiter in den for case laufen, wo iterierung über die Fälle läuft

//
    //alle start möglichkeiten nach einer Rekursion einsammeln (getStartPossibilities schreibt die neuen Startwerte ins Arr)
    local int applRecFoundCount=1;
    local int possibleRecEndArr[0];
    local int possibleRecEndArrLen=1;
    possibleRecEndArr+=currStackCount;
    while(applRecFoundCount>0){
        //getStartPossibilities(recEndArr, currArrRecursionBegin,currArrRecursionLen,currArrLen, recursionCount, recursionStartPosition)
        
        //____an diese wege muss die rekursion angehängt werden
        //possibleRecEndArr=wo rekursion aufhören könnte -> ab da muss dann isSpecificPosition getestet werden
        //possibleRecEndArrLen=länge des arrays, was sagt wo rekursion aufhören könnte 
        //applRecFoundCount= nur an diesen letzten x wegen soll wieder rekursion ausprobiert werden
        //____mögliche Wege für Rekursion -> e.g. "<T>", "<R>", "(<R> end)", "$3" und "<T>", "<F>", "_", "(<F> end)", "$4"
        //recursionBegins= der beginn aller möglichen rekursionswege -> darüber muss iteriert werden
        //recursionLenArr= länge aller rekursionswege -> passender index zu recursionBegins
        //recursionCount= anzahl der rekursionsmöglichkeiten
        
        applRecFoundCount=getStartPossibilities(positionToProof, possibleRecEndArr, possibleRecEndArrLen, applRecFoundCount, recursionBegins,recursionLenArr,recursionCount);
        possibleRecEndArrLen=possibleRecEndArrLen+applRecFoundCount;
    }
    
    return possibleRecEndArr[possibleRecEndArrLen-1];
    //addListInt(possibleRecEndArr,possibleRecEndArrLen-1, checkContinueArr,0);
    //return possibleRecEndArrLen;

}


//EINSCHRÄNKUNGEN: in der rtekursion darf nicht dont care ("_") sein oder eine weitere rekursion ("$")
int checkSingleRecursion(string positionToProof [], int arrLen,int proofValLen, int indexToBegin){
    local int i;
    local int currStackCount=indexToBegin;
    for(i=0; i<proofValLen; i++){

        if(currStackCount<0 ){
            return indexToBegin;
        }   

        local string currArrContent=positionToProof[arrLen-1-i];
        if(currArrContent=="_"){
            //es wird davon ausgegangen, dass es nur einen parent gibt auf den Beschreibung zutrifft
            currStackCount = nontermStackId[currStackCount+1];

        }else{
            local byte positionAndStackHasDiffValue = currArrContent!=nontermStack[currStackCount];
            if(positionAndStackHasDiffValue){
                local byte stackValIsDerivationRule = nontermStack[currStackCount][0]=='{';
                if(stackValIsDerivationRule){
                    i=i-1;
                }else{
                    return indexToBegin;
                }
            }
            currStackCount =currStackCount-1;
        }
    }
    return currStackCount;
}

int getStartPossibilities(string positionToProof [], int possibleRecEndArr [], int possibleRecEndArrLen, int applRecFoundCount, int recursionBegins[],int recursionLenArr[],int recursionCount){
    //____an diese wege muss die rekursion angehängt werden
        //possibleRecEndArr=wo rekursion aufhören könnte -> ab da muss dann isSpecificPosition getestet werden
        //possibleRecEndArrLen=länge des arrays, was sagt wo rekursion aufhören könnte 
        //applRecFoundCount= nur an diesen letzten x wegen soll wieder rekursion ausprobiert werden
    //____mögliche Wege für Rekursion -> e.g. "<T>", "<R>", "(<R> end)", "$3" und "<T>", "<F>", "_", "(<F> end)", "$4"
        //recursionBegins= der beginn aller möglichen rekursionswege -> darüber muss iteriert werden
        //recursionLenArr= länge aller rekursionswege -> passender index zu recursionBegins
        //recursionCount= anzahl der rekursionsmöglichkeiten
//applRecFoundCount=getStartPossibilities(positionToProof, possibleRecEndArr, possibleRecEndArrLen, applRecFoundCount, recursionBegins,recursionLenArr,recursionCount);
 
    
    local int recFoundCount=0;
    local int i=0;
    local int j=0;
    for(j=possibleRecEndArrLen-applRecFoundCount; j<possibleRecEndArrLen; j++){//iteriere über gefundene Rekursionswege
        for(i=0; i<recursionCount; i++){//iteriere über mögliche rekursionen -> e.g. "<T>", "<R>", "(<R> end)", "$3" und "<T>", "<F>", "_", "(<F> end)", "$4"
            local int currArrRecursionBegin=recursionBegins[recursionCount-1-i];//JEWEILIGE REKURSION BEGINNT HIER
            local int currArrRecursionLen=recursionLenArr[recursionCount-1-i];//JEWEILIGE REKURSION BEGINNT HIER

            local int currPositionNontermStack=possibleRecEndArr[j];//nonterm stack beginnt gerade hier

            local int newCurrPositionNontermStack=checkSingleRecursion( positionToProof, currArrRecursionBegin, currArrRecursionLen, currPositionNontermStack);
            local byte recApplicable=currPositionNontermStack-newCurrPositionNontermStack>0;

            if(recApplicable){
                possibleRecEndArr+=newCurrPositionNontermStack;
                recFoundCount=recFoundCount+1;
            }
        }
    }
    return recFoundCount;
}




int handleDontCare(string positionToProof [],int arrLen, int currStackCount, int checkContinueArr[]){
    local int localStackCount=currStackCount;

    //handler special case ["<T>","_","(<T> end)"]
    local string parentToProof=positionToProof[arrLen-2];
    local string beforeDontCare=positionToProof[arrLen];

    if(beforeDontCare[0]=='('){
        local int i=0;
        while(True){
            //compare 2 strings symbol for symbol
            if(beforeDontCare[i+1]!=parentToProof[i]){
                if(beforeDontCare[i+1]==' ' && parentToProof[i]=='\\0'){
                    //"<T>","_","(<T> end)" found
                    local int arrAdd=nontermStackId[currStackCount+1];
                    checkContinueArr+=arrAdd;
                    return 1;
                }
                break;
            } 
            i=i+1;
        }
    }


    local string currStackVal=nontermStack[currStackCount];
    local int possibilitiesFound=0;
    if(currStackVal==parentToProof){
        possibilitiesFound=possibilitiesFound+1;
        checkContinueArr+=localStackCount;
        }

    while(localStackCount>0){
        localStackCount=localStackCount-1;
        
        currStackVal=nontermStack[localStackCount];

        //fitting parent found -> success
        if(currStackVal==parentToProof){
            possibilitiesFound=possibilitiesFound+1;
            checkContinueArr+=localStackCount;
        }

        //close Tag found -> überspringen
        if(currStackVal[0]=='('){
            local int nontermBegin= nontermStackId[localStackCount];
            localStackCount=nontermBegin;
        }
    }
    return possibilitiesFound;
}


byte isSpecificPosition(string positionToProof [], int arrLen, int indexToBegin){
    local int id=getIndexOfSpecificPosition(positionToProof, arrLen, indexToBegin);
    return id!=-1;
}



//returnt index von Position 0 von positionToProof
//e.g. 
//local string nontermStack[]={..., "<EE>", "(<EE> end)", "(<E> end)"};
//local int nontermStackId[]={..., 13, 13, 5 };
//local int nontermStackIndex=15;
//local string positionToProof[]={"(<EE> end)","(<E> end)"};
//-> returnt 14
int getIndexOfSpecificPosition(string positionToProof [], int arrLen, int indexToBegin){
    local int checkContinueArr []={indexToBegin};//speichert die optionen, die nach sonderzeichen überprüft werden müssen
    local int arrLenContinueArr []={arrLen};//speichert die optionen, die nach sonderzeichen überprüft werden müssen
    local int checkContinueArrIndex=0;
    local int checkContinueArrPointer=-1;


    while (checkContinueArrIndex>checkContinueArrPointer){//iteriert über alle continue array teile
        local int currStackCount;
        local int myArrLen;
            checkContinueArrPointer=checkContinueArrPointer+1;
            if(checkContinueArrIndex>=checkContinueArrPointer){
                currStackCount=checkContinueArr[checkContinueArrPointer];
                myArrLen=arrLenContinueArr[checkContinueArrPointer];
                local string currArrContent=positionToProof[myArrLen-1];
            }else{
                return -1;
            }

    local int i;
    for(i=0; i<myArrLen; i++){//geht einen checkContinueArrIndex durch

        if(currStackCount<0 ){//gehe zurück in die while schleife
            break;
        }   

        local string currArrContent=positionToProof[myArrLen-1-i];
        //dont care handling
        if(currArrContent=="_"){
            //es wird davon ausgegangen, dass es nur einen parent gibt auf den Beschreibung zutrifft
            local int possibilitiesFound = handleDontCare(positionToProof,myArrLen-i, currStackCount, checkContinueArr);
            checkContinueArrIndex=checkContinueArrIndex+possibilitiesFound;
            local int j;
            for (j=0; j<possibilitiesFound; j++){
                local int continueVal=myArrLen-i-1;
                arrLenContinueArr+=continueVal;
            }
            break;
            
        }else if(currArrContent[0]=='$'){//handle recursion
            //es wird davon ausgegangen, dass es nur einen parent gibt auf den Beschreibung zutrifft

            currStackCount = handleRecursion(positionToProof,myArrLen-i, currStackCount);
            //local int possibilitiesFound = handleRecursion(positionToProof,myArrLen-i, currStackCount, checkContinueArr);
            //checkContinueArrIndex=checkContinueArrIndex+possibilitiesFound;

            while(currArrContent[0]=='$'){//while new recursion rule seen
                local string s2= SubStr( currArrContent, 1 );
                local int currRecLen=Atoi(s2);
                i=i+1 + currRecLen;
                currArrContent=positionToProof[myArrLen-1-i];
            }
            i=i-1;//der value muss noch mal geprüft werden
            //local int j;
            //for (j=0; j<possibilitiesFound; j++){
            //    local int continueVal=myArrLen-i-1;
            //    arrLenContinueArr+=continueVal;
            //}
            //break;
        }else{
            local byte positionAndStackHasDiffValue = currArrContent!=nontermStack[currStackCount];
            if(positionAndStackHasDiffValue){
                local byte stackValIsDerivationRule = nontermStack[currStackCount][0]=='{';
                if(stackValIsDerivationRule){
                    currStackCount=currStackCount-1;
                    i=i-1;//der value muss noch mal geprüft werden
                }else{
                    break;
                }
            }
            currStackCount =currStackCount-1;
        }
    }
    if(i==myArrLen){
    return currStackCount+1;
    }
}
return -1;
}




//____________isSpecificPosition_END_________________
""" 

        stack="""
local string nontermStack[0];
local int nontermStackId[0];
local int nontermStackIndex=-1;
"""

        debugFunction="""
//BEGIN_debug_functions
byte printFullStringStack(string txt, int upperBound, int lowerBound, string stack []){
    local int i;   
        
    Printf("\\n"); 
    //Printf("%s\\n",txt); 
    //Printf("lowerBound: %i\\n",lowerBound); 
    //Printf("upperBound: %i\\n",upperBound); 
    for(i=lowerBound; i<=upperBound; i++) {
        Printf("\\"%s\\", ",stack[i]);
    }
    Printf("\\n");
    return True;
}
byte printFullIntStack(string txt, int upperBound, int lowerBound, int stack []){
    local int i;   
        
    Printf("\\n"); 
    //Printf("%s\\n",txt); 
    //Printf("lowerBound: %i\\n",lowerBound); 
    //Printf("upperBound: %i\\n",upperBound); 
    for(i=lowerBound; i<=upperBound; i++) {
        Printf("%i, ", stack[i]);
    }
    Printf("\\n");
    return True;
}
//END_debug_functions
        """

        helpFunctions="""
int getUnequalWithStack(string compareStack [], int compareStackIndex, string   avoidStack [], int avoidStackIndex){
    local int resultLen=compareStackIndex;
    local int i;
    for (i=0; i<=avoidStackIndex; i++){
        compareStack-=avoidStack[i];
        resultLen=resultLen-1;
    }
    return resultLen;
}

byte deleteList(string list[],int listLen){
    local int i;
    for(i=0;i<listLen;i++){
        list-=list[i];
    }
}

byte existDiffValInStack(string arr [], int arrLen){
    local int i;
    for(i=1;i<arrLen;i++){
        if(arr[i]!=arr[0]){
            return True;
        }
    }
    return False;
}
        
byte findInStringArray(string s, string arr [], int arrLen){
    local int i;
    for(i=0;i<arrLen;i++){
        if(arr[i]==s){
            return i;
        }
    }
    return -1;
}
byte isInStringArray(string s, string arr [], int arrLen){
    return findInStringArray( s, arr, arrLen)>-1;
}

byte findInIntArray(int s, int arr [], int arrLen){
    local int i;
    for(i=0;i<arrLen;i++){
        if(arr[i]==s){
            return i;
        }
    }
    return -1;
}

//returnt neue arr len
byte removeFromStackByIndex(int index, string stack_val [],int stackId [], int arrLen){
    local int newArrLen=arrLen-1;
    stack_val-=stack_val[index];
    stackId-=stackId[index];
    return newArrLen;
}

byte isInIntArray(int s, int arr [], int arrLen){
    return findInIntArray( s, arr, arrLen)>-1;
}


byte removeFromStackWithIndex(int index, string stack_val [], int currIndex){
    local int newIndex=currIndex-1;
    local int i;
    for(i=index;i<newIndex;i++){
        stack_val[i]=stack_val[i+1];
    }
    return newIndex;
}
        """
        
        libForm_quantorExpression={
            "globalInfo":[stack,findSpecificPosition,helpFunctions,debugFunction],
        }

        #generate preferd Values
        self.libForm_pref_possible(libForm_quantorExpression, fullQuantorExpression, isPref=True,grammar=grammar)
        #generate Possible Values
        self.libForm_pref_possible(libForm_quantorExpression, fullQuantorExpression, isPref=False,grammar=grammar)
        self.libForm_prefChance(libForm_quantorExpression, fullQuantorExpression,grammar)

        for constraint in fullQuantorExpression:
            self.libForm_quantorExpression_forConstraint(constraint, libForm_quantorExpression,grammar)
            
            
        return libForm_quantorExpression

    def libForm_prefChance(self, libForm_quantorExpression, fullQuantorExpression, grammar):

        info={}
        for constr in fullQuantorExpression:
            constr.addPrefChanceByStackType(info)
        #[self.varType] = {"stackLocation":self.stackLocation,"var":self.var,"prefChance":self.preferedChanche["prefChance"],"conditions":self.preferedChanche["conditions"] }

        for nonterm in grammar:
            prefChanceArr=[]
            if(not nonterm in info):
                libForm_quantorExpression[nonterm]["pref_chance"]=NoPrefChanceDeclared().__str__()
                continue
        
            prefChanceArr=info[nonterm]

            #create a new entry in libform for non-terminal type
            if(not nonterm in libForm_quantorExpression):
                libForm_quantorExpression[nonterm]={}


            prefChanceToken=NoPrefChanceDeclared()

            atLeast1ValNot1 = any(not math.isclose(GlobalDefines.STANDARD_PREF_POSSIBILITY ,element["prefChance"], abs_tol=0.001) for element in prefChanceArr)
            if(atLeast1ValNot1):
                #order arr by pref chance (niedrigstens ganz oben)
                sortedPrefChanceArr = sorted(prefChanceArr, key=lambda x: x["prefChance"])
                for val in sortedPrefChanceArr:
                    stackLocArr=StackLocationArr(val["var"],val["stackLocation"])
                    condition=self.generateConstraintConditionToken(stackLocArr,val["conditions"])
                    currValAction=Conditional(condition, PrefChance(val["prefChance"]))
                    prefChanceToken=SequentialExecution(prefChanceToken,currValAction)      

            libForm_quantorExpression[nonterm]["pref_chance"]=prefChanceToken.__str__()



    def libForm_pref_possible(self, libForm_quantorExpression, fullQuantorExpression, isPref,grammar):

        info={}
        #create pref und ṕossible info
        for constr in fullQuantorExpression:
            if(isPref):
                constr.addPrefValByStackType(info)
            else:
                constr.addPossibleValByStackType(info)

        #handle multple prefered infos 
        for nonterm in grammar:
            #create a new entry in libform for non-terminal
            if(not nonterm in libForm_quantorExpression):
                libForm_quantorExpression[nonterm]={}
            commonToken=PrefNotFound() if isPref else PossibleNotFound()

            if(nonterm in info):

                prefArr=info[nonterm]

                number_of_possible_unions=self.get_number_of_possible_unions(len(prefArr))
                unionsArr=[None] * number_of_possible_unions
                valuesWithSpecificValue=[None] * len(prefArr)
                for x in range(number_of_possible_unions):
                    currSetTotal=None
                    currVal=x+1
                    usedArrParts=0
                    for unionNr in range(len(prefArr)-1,-1, -1):
                        if currVal-pow(2, unionNr)>=0:
                            usedArrParts+=1
                            currVal=currVal-pow(2, unionNr)
                            currSet=set(prefArr[unionNr]["prefArr"]["values"])
                            if(currSetTotal!=None):
                                currSetTotal=currSetTotal & currSet
                            else:
                                currSetTotal=currSet
                    infoPrefPoss=Prefered(ArrToStack(currSetTotal)) if isPref else Possible(ArrToStack(currSetTotal)) 
                    tokenInfo=infoPrefPoss if(currSetTotal and bool(currSetTotal)) else None
                    unionsArr[x]={"set":currSetTotal,"stackVariations":[],"token":tokenInfo}
                    if(valuesWithSpecificValue[usedArrParts-1]==None):
                        valuesWithSpecificValue[usedArrParts-1]=[]
                    valuesWithSpecificValue[usedArrParts-1].append(x)
            
                #get stack combos + handle stack
                for x in range(len(unionsArr)):
                    currVal=x+1
                    usedArrParts=[]
                    for unionNr in range(len(prefArr)-1,-1, -1):
                        if currVal-pow(2, unionNr)>=0:
                            usedArrParts.append(unionNr)
                            currVal=currVal-pow(2, unionNr)
                
                    # iterate over array with usedArrParts to see which stack combinations are possible
                    parentCombinations=self.get_number_of_possible_unions(len(usedArrParts))
                    for parentCombi in range(parentCombinations-1,-1, -1):
                        currVal=parentCombi+1
                        usedArrPartsStackCombi=[]
                        for arrIndex in range(len(usedArrParts)-1,-1, -1):
                            if currVal-pow(2, arrIndex)>=0:
                                usedArrPartsStackCombi.append(arrIndex)
                                currVal=currVal-pow(2, arrIndex)

                        #breakout conditions -> in these cases no prefered values have to be created
                        usedValSet=set(usedArrPartsStackCombi)
                        if usedValSet in unionsArr[x]["stackVariations"]:
                            continue
                        cont=False
                        for prefArrIndex in usedArrPartsStackCombi:
                            #only combinations where all sets have a stack need to be checked
                            if(prefArr[usedArrParts[prefArrIndex]]['prefArr']['arrays']==[] and prefArr[usedArrParts[prefArrIndex]]['prefArr']['notEqualsWithArr']==[]):
                                cont=True
                                break
                        if(cont):
                            continue
                        #if the union of all remaining values is zero
                        valueNeeded=0
                        commonSet=set()
                        for val in usedArrPartsStackCombi:
                            valueNeeded+=pow(2,usedArrParts[val])
                            #set(a & b & c)-set(a)-set(b) instead of set(a & b & c)-set(a & b), because the stacks of a and b are still checked individually and so no common set is checked twice
                            commonSet.update(unionsArr[pow(2,usedArrParts[val])-1]["set"])

                        
                        commonValWithoutCurrSets=unionsArr[x-valueNeeded]["set"]-commonSet
                        if(len(usedArrPartsStackCombi)!=len(usedArrParts) and not bool(commonValWithoutCurrSets)):
                            continue


                        unionsArr[x]["stackVariations"].append(usedValSet)
                        stackListsList=[]
                        for prefArrIndex in usedArrPartsStackCombi:
                            stackList=prefArr[usedArrParts[prefArrIndex]]['prefArr']['arrays']
                            avoidList=prefArr[usedArrParts[prefArrIndex]]['prefArr']['notEqualsWithArr']
                            stackListsList.append({"stackList":stackList,"avoidList":avoidList} )
                        unionsArr[x]["token"]=SequentialExecution(unionsArr[x]["token"],AddToPrefPossibleIfValInStack(stackListsList,commonValWithoutCurrSets,isPref))

                #combine parts of array
                #valuesWithSpecificValue=[[0, 1, 3], [2, 4, 5], [6]]
                commonToken=PrefNotFound() if isPref else PossibleNotFound()
                for arrWithStackNr in valuesWithSpecificValue:#[2, 4, 5]
                    for nr in arrWithStackNr:#2
                        if(unionsArr[nr]["token"]):
                            #get beteiligte array teile
                            currVal=nr+1
                            usedArrParts=[]
                            for unionNr in range(len(prefArr)-1,-1, -1):
                                if currVal-pow(2, unionNr)>=0:
                                    usedArrParts.append(unionNr)
                                    currVal=currVal-pow(2, unionNr)

                            commonConstraintConditionToken=None
                            #create if condition 
                            for part in usedArrParts:
                                stackLocArr=StackLocationArr(prefArr[part]["var"],prefArr[part]["stackLocation"])
                                constraintConditionToken=self.generateConstraintConditionToken(stackLocArr,prefArr[part]["conditions"])
                                commonConstraintConditionToken=And(commonConstraintConditionToken,constraintConditionToken)
                            commonToken=Conditional(commonConstraintConditionToken,unionsArr[nr]["token"],commonToken)
                    

            locationToAddInfo ="prefered" if isPref else "possible"
            libForm_quantorExpression[nonterm][locationToAddInfo]=commonToken.__str__()
            


    def decimalToBinary(n,totalNr):
        return f"{{0:0{totalNr}b}}".format(int(n))
    
    def get_number_of_possible_unions(self, number_of_elements):
        unionNr=0
        for i in range(number_of_elements):
            unionNr+=math.comb(number_of_elements, i)
        return unionNr
    
    def hasVariable(self,var):
        if(self.spezification):
            varsInSpez = re.findall('\{<[A-Za-z][A-Za-z0-9_-]*> ([A-Za-z][A-Za-z0-9_-]*)\}', self.spezification) 
            return (var in varsInSpez) or self.elemName==var
        return self.elemName==var
                
    def getAllVariables(self):
        if( not self.spezification):
            return []
        return re.findall('\{<[A-Za-z][A-Za-z0-9_-]*> ([A-Za-z][A-Za-z0-9_-]*)\}', self.spezification) +[self.elemName]   

    def getFirstVariableInExpression(self, var1,var2, operation):
        if(var1==var2):
            raise ValueError("this is not supported")

        hasVar1=self.hasVariable(var1)
        hasVar2=self.hasVariable(var2)
        if (hasVar1 and hasVar2):
            allVarInSpez=re.findall('\{<[A-Za-z][A-Za-z0-9_-]*> ([A-Za-z][A-Za-z0-9_-]*)\}', self.spezification)
            if(allVarInSpez.index(var1)<allVarInSpez.index(var2)):
                return var1
            else:
                return var2
        else:
            if(operation=="before" and (hasVar1 or hasVar2)):
                recVar=var1 if hasVar2 else var2
                quantorexpr=self.upperQuantorExpression
                while quantorexpr:
                    if(quantorexpr.hasVariable(recVar)):
                        return recVar
                    quantorexpr=quantorexpr.upperQuantorExpression
                return None
            if(self.upperQuantorExpression):
                return self.upperQuantorExpression.getFirstVariableInExpression(var1,var2, operation)
            else:
                return None


        
    def getSpecificationWithoutVariables(self):
        return re.sub(r'\{(<[A-Za-z][A-Za-z0-9_-]*>) [A-Za-z][A-Za-z0-9_-]*\}',r"\1", self.spezification)
    
    def getSpezificationAfter(self, var):
        return re.sub(r'\{(<[A-Za-z][A-Za-z0-9_-]*>) [A-Za-z][A-Za-z0-9_-]*\}',r"\1",self.spezification.split(f"{var}}}")[1])

    def getSpezificationUntil(self, var):
        splitted=re.split(rf'{{(<[A-Za-z][A-Za-z0-9_-]*>) {var}}}', self.spezification)
        return re.sub(r'\{(<[A-Za-z][A-Za-z0-9_-]*>) [A-Za-z][A-Za-z0-9_-]*\}',r"\1",splitted[0])+splitted[1]



    def createAllPossibleFirstNonterms(self, parent, firstNonterms,allPossibleFirstNonterms):
        for firstNonterm in firstNonterms[parent]:
            first=firstNonterm[0]
            if not (first in allPossibleFirstNonterms):
                allPossibleFirstNonterms.add(first)
                self.createAllPossibleFirstNonterms(first, firstNonterms,allPossibleFirstNonterms)



    #returns possible derivations parent and child
    #e.g. for simple grammar: <start> to <T> returns parentLocations=[['<start>', '<E>', '<T>']]
    def findConnectionArrayBetweenFirstOfNonterms(self, firstNonterms, childType, currParentLocation, parentLocations ):
        inbetweenNonterms=firstNonterms[currParentLocation[-1]]

        for nonterm in inbetweenNonterms:
            
            if(nonterm[1]=="Epsilon"):
                parentWithEps=currParentLocation[-1]
                currParentLocation.append("_")
                currParentLocation.append(f"({parentWithEps} end)")

            currParentLocation.append(nonterm[0])

            if(nonterm[0]==childType):
                parentLocations.append(currParentLocation.copy())
            else:
                self.findConnectionArrayBetweenFirstOfNonterms(firstNonterms, childType,  currParentLocation, parentLocations )
            currParentLocation.pop()
            if(nonterm[1]=="Epsilon"):
                currParentLocation.pop()
                currParentLocation.pop()

    def handleDontCare(self,parentArr, parentIndex, childArr,childIndex, parentLocations,grammar):

        inbetweenSteps=[]
        for index in range(parentIndex,-1,-1):
            inbetweenSteps.append(parentArr[index])
            if(parentArr[index]==childArr[childIndex]):
                self.findParentsForSpecificRule(index,parentArr,childArr,childIndex, parentLocations,grammar)

    def findParentsForSpecificRule(self,parentIndex,parentArr,childArr,childIndex, parentLocations, grammar):
        
        indexAusgleich=0
        indexHelp=parentIndex+1
        while indexHelp+indexAusgleich>=0:
            indexHelp-=1


            index=indexHelp+indexAusgleich
            parentVal=parentArr[index]
            childVal=childArr[childIndex] 
            
            #both values have the form (<...> end) and are not the same values
            if(parentVal==childArr[childIndex]):
                if(childIndex==0):
                    parentLocations.append([parentArr[0]])
                    break
                elif(index<=0):
                    newParentConnection=childArr[:childIndex+1]
                    parentLocations.append(newParentConnection)
                    break
                childIndex=childIndex-1
            elif(re.match("\$[1-9][0-9]*",childVal)):
                #restructure the recursion further backwards
                recursionIndex=childIndex-1
                indexAfterRecursion=recursionIndex-int(childVal[1:])
                recursionLen=int(childVal[1:])
                newChildArr=childArr[:indexAfterRecursion+1].copy()
                i=0
                while(childArr[recursionIndex-i]==childArr[indexAfterRecursion-i] and recursionLen-i>0):
                    i+=1
                i-=1

                if(i==0):
                    #recursion found, skip
                    childIndex=childIndex-int(childVal[1:])-1
                elif i==-1:
                    #try to use recursion
                    childIndex-=1
                    index=indexHelp+indexAusgleich 
                    parentVal=parentArr[index]
                    childVal=childArr[childIndex] 
                else:
                    #append recursion earlier in stack
                    for derivationRule in childArr[indexAfterRecursion+1:recursionIndex-i][::-1]:
                        newChildArr.append(derivationRule)

                    newChildArr.append(childVal)
                    for derivationRule in childArr[recursionIndex-i:recursionIndex+1]:
                        print("append dinge vor recursion rule jetzt danach: derication rule to append: ", derivationRule)
                        newChildArr.append(derivationRule)
                    childArr=newChildArr   

                indexAusgleich=indexAusgleich+1
                
                childVal=childArr[childIndex] 
            elif(re.match("^\(<[a-zA-Z-_]+> end\)",parentVal) and re.match("^\(<[a-zA-Z-_]+> end\)",childArr[childIndex])):

                normalOfEnd=getBeginFromEndStackLocation(childArr[childIndex])
                childDerivationRules=grammar[normalOfEnd]
                for devRule in childDerivationRules:
                    endsWithNonterm=expressionEndsWithNonterminal(devRule)
                    lastNonterm=findLastNonTerminal(devRule)
                    if(endsWithNonterm and lastNonterm==getBeginFromEndStackLocation(parentVal)):
                        newChildArr=childArr.copy()
                        newChildArr=newChildArr[:childIndex-1]

                        
                        
                        for nonterm in findAllNonTerminal(devRule)[:-1]:
                            newChildArr.append(nonterm)
                            newChildArr.append("_")
                            newChildArr.append(f"({nonterm} end)")




                        recursiveRules=getEndRecursiveRule(lastNonterm, grammar[lastNonterm])
                        for recursiveRule in recursiveRules:
                            recursionLen=1
                            newChildArr.append(lastNonterm)
                            for nonterm in findAllNonTerminal(recursiveRule)[:-1]:
                                newChildArr.append(nonterm)
                                newChildArr.append("_")
                                newChildArr.append(f"({nonterm} end)")
                                recursionLen+=3
                            newChildArr.append(f"${recursionLen}")
                        
                        


                        newChildArr.append(lastNonterm)
                        newChildArr.append("_")
                        self.findParentsForSpecificRule(index-1,parentArr,newChildArr,len(newChildArr)-1, parentLocations, grammar)
                    break
            elif(isSpezRule(childArr[childIndex])):
                indexAusgleich=indexAusgleich+1
                childIndex=childIndex-1
            elif(childArr[childIndex] == "_"):
                newParentConnection=[]
                for item in childArr[:childIndex+1]:
                    newParentConnection.append(item)
                newParentConnection.append(parentArr[0])# parentConn[0] ist parent nonterm

                parentLocations.append(newParentConnection)
                return self.handleDontCare(parentArr, index, childArr,childIndex-1, parentLocations, grammar)
            elif(parentVal != childArr[childIndex]):
                break



    def findParentStackLocations(self, firstNonterms, childType, childStackLocation, currParentLocation, parentLocations,grammar ):
        parentConnections=[]
        self.findConnectionArrayBetweenFirstOfNonterms(firstNonterms,childType, currParentLocation, parentConnections  )

        #iterate over possible connections ways
        #e.g. parentConn=['<start>', '<E>', '<T>', '<F>'] ; parentConnections=[['<start>', '<E>', '<T>','<F>']]
        for parentConn in parentConnections:
            #iterate over nonterminal in one connection Way 
            #e.g. nonterm='<F>' (=parentConn[-1]) ; parentConn[::-1]=['<F>','<T>', '<E>', '<start>'] 
            
            i=len(childStackLocation)-1
            if(i<0): return
            self.findParentsForSpecificRule(len(parentConn)-1,parentConn,childStackLocation,i, parentLocations, grammar)


    def getParentPrefChance(self, prefChance, rulesCount):
        newConditionsArr=[]
        for condition in prefChance["conditions"]:
            if(condition["isParentApplicable"]==True):
                newConditionsArr.append(condition)
            else:
                raise ValueError("Not implemented: isParentApplicable!=True")
        
        newPrefChance={
            "prefChance":prefChance["prefChance"]/rulesCount,
            "conditions":newConditionsArr
        }
        return newPrefChance


    #copy prefered/possible value to derivation determining non-terminal
    def copyPrefPossibleForParent(self, libForm_quantorExpression,firstNonterms,key,table, grammar):
        newConstraints=[]
        allPossibleFirstNonterms={}

        for key in firstNonterms:
            allPossibleFirstNonterms[key]=set()
            self.createAllPossibleFirstNonterms(key, firstNonterms, allPossibleFirstNonterms[key])


        #e.g. '<start>': {'<E>', '<T>', '<F>'}
        for key,firstNontermsOfKey in allPossibleFirstNonterms.items():



            #e.g. <E> in {'<E>', '<T>', '<F>'} 
            for firstNonterm in firstNontermsOfKey:
                for constr in libForm_quantorExpression:
                
                    if firstNonterm == constr.varType:
                        parentPositionName=GlobalDefines.normalize('parentPosition', GlobalDefines.ISLA_RULE)

                        if constr.preferedValues or constr.possibleValues:
                            parentLocations=[]
                            self.findParentStackLocations(firstNonterms,constr.varType, constr.stackLocation,[key], parentLocations,grammar  )
                           
                            # no derivation determining non-terminal found
                            if(parentLocations==[]):
                                continue
                            newConstr=Constraint(var=parentPositionName,varType=key, stackLocation=parentLocations)
                            
                            additionalFirst=createFirstTableForExp(key, grammar, [firstNonterm])
                            if("" in grammar[key]):
                                follow_Table = createFollow_dict(grammar)
                                additionalFirst=additionalFirst.union(follow_Table[key])

                            #handle prefered -> add all prefered Values of child in this List
                            if constr.preferedValues:
                                normalFirst=copy.deepcopy(constr.preferedValues["prefArr"])
                                if(len(additionalFirst)>0 and not normalFirst["notEqualsWithArr"]):#dont add additional items if exclusion is made
                                    normalFirst["values"]=list(normalFirst["values"])+list(additionalFirst)#hiers
                                    
                                newConditions=[]
                                for condition in constr.preferedValues["conditions"]:
                                    if(condition["isParentApplicable"]==True):
                                        newConditions.append(condition)
                                    else:
                                        raise ValueError("isParentApplicable=False not supported ")
                                
                                
                                newPrefValues={
                                    "prefArr":normalFirst,
                                    "conditions":newConditions
                                }

                                newConstr.preferedValues=newPrefValues
                            
                            if(constr.preferedChanche):
                                if(type(constr.preferedChanche)==type([])):
                                    newConstr.preferedChanche=[]
                                    for prefChance in constr.preferedChanche:
                                        newConstr.preferedChanche.append(self.getParentPrefChance(prefChance, len(grammar[key])))
                                else:
                                    newConstr.preferedChanche=self.getParentPrefChance(constr.preferedChanche, len(grammar[key]))

                            #handle possible -> add all possible Values of child in this List
                            if constr.possibleValues:
                                normalFirst=copy.deepcopy(constr.preferedValues["prefArr"])
                                if(len(additionalFirst)>0 and not normalFirst["notEqualsWithArr"]):#dont add additional items if exclusion is made
                                    normalFirst["values"]=list(normalFirst["values"])+list(additionalFirst)

                                newConditions=[]
                                for condition in constr.possibleValues["conditions"]:
                                    if(condition["isParentApplicable"]==True):
                                        newConditions.append(condition)
                                    else:
                                        raise ValueError("isParentApplicable=False not supported ")
                            
                            
                                newPossibleValues={
                                    "prefArr":normalFirst,
                                    "conditions":newConditions
                                }

                                newConstr.possibleValues=newPossibleValues
                            newConstraints.append(newConstr)
                    

            
        for constr in newConstraints:
            constr.printAttributes()
            libForm_quantorExpression.append(constr)

        


    def getFollowNonterms(self, s, grammar, followTable, nontermsSeen=[]):
        if(not s in followTable):
            followTable[s] = set()
        
        for key in grammar:
            for value in grammar[key]:#derivation rules
                derivationRuleCountWithS = value.find(s)
                if derivationRuleCountWithS > -1:
                    if value.endswith(s): 
                        if key != s and not (key in nontermsSeen):  # no recursive derivation rule
                                nontermsSeen.append(key)
                                self.getFollowNonterms( key, grammar, followTable, nontermsSeen)
                                myTuple=[(item[0], "Epsilon") for item in followTable[key]]
                                followTable[s].update(myTuple)
                    else: 
                        valueAfterS = value[derivationRuleCountWithS+len(s):]
                        if(expressionStartsWithNonterminal(valueAfterS)):
                            followTable[s].add((findFirstNonTerminal(valueAfterS), "Epsilon"))
        return followTable


    #get derivation defining non-terminals and apply prefered/possible values for Lookahead function
    def createParentInfo(self, grammar, libForm_quantorExpression):
        """
        table = {
                nontermName1:{
                        prefered:[]
                        possible:[]
                        pref_chance:1
                    },
                nontermName2:{
                        prefered:[]
                        possible:[]
                        pref_chance:1
                    },
                ...
                }
        -> dann benutze diese infos zusammen mit transition Table, um rauszufinden was bei welcher Regel gemacht werden muss
        """
        table = {}
        for key in grammar:
            table[key]=set()
            for derivationRule in grammar[key]:
                
                #if derivation rule is epsilon, get follow
                if  derivationOptionIsEpsylon(derivationRule):
                    followNonterms=self.getFollowNonterms(key, grammar, {})[key]
                    table[key].update(followNonterms)

                #get first non-terminal of derivation Rule
                if expressionStartsWithNonterminal(derivationRule):
                    firstNonterm=findFirstNonTerminal(derivationRule)
                    table[key].add((firstNonterm, None))

        self.copyPrefPossibleForParent(libForm_quantorExpression,table,key,table, grammar)
