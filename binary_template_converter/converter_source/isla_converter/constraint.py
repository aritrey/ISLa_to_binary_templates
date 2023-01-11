

import pprint
from typing import List
from isla_converter.isla_token import Token

class Constraint():
    def __init__(self,var:str=None,varType:str=None,globalInfo:List[Token]=None,stackLocation:List[str]=None,preferedValues:Token=None,preferedChanche:Token=None,possibleValues:Token=None,backtrace:Token=None,operation:List[Token]=None,structBegin:List[Token]=None,structEnd:List[Token]=None,trueIndicator:Token=None) -> None:
        self.var=var
        self.varType=varType
        self.globalInfo=globalInfo
        self.stackLocation=stackLocation
        self.preferedValues=preferedValues
        self.preferedChanche=preferedChanche
        self.possibleValues=possibleValues
        self.backtrace=backtrace
        self.operation=operation
        self.structBegin=structBegin
        self.structEnd=structEnd
        self.trueIndicator=trueIndicator 
    
    def printAttributesAsString(self):
        pp = pprint.PrettyPrinter(indent=4)

        if(self.preferedValues != None):
            printablePrefArr=[]
            for condition in self.preferedValues["conditions"]:
                printablePrefArr.append({"condition":condition["condition"].__str__(), "isParentApplicable": condition["isParentApplicable"]})
            

        if(self.possibleValues != None):
            printablePossibleArr=[]
            for condition in self.possibleValues["conditions"]:
                printablePossibleArr.append({"condition":condition["condition"].__str__(), "isParentApplicable": condition["isParentApplicable"]})
        

        
        pp.pprint({
            "var":self.var,
            "varType":self.varType,
            "globalInfo":[item.__str__() for item in  self.globalInfo] if self.globalInfo else None,
            "stackLocation":self.stackLocation,
            "preferedValues":{"prefArr":self.preferedValues["prefArr"],"conditions":printablePrefArr} if self.preferedValues!=None else None,
            "preferedChanche":self.preferedChanche,
            "possibleValues":{"prefArr":self.possibleValues["prefArr"],"conditions":printablePossibleArr} if self.possibleValues!=None else None,
            "backtrace":self.backtrace,
            "operation":self.operation.__str__() if(self.operation) else None,
            "structBegin":[item.__str__() for item in  self.structBegin] if self.structBegin else None,
            "structEnd":[item.__str__() for item in self.structEnd] if self.structEnd else None,
            "trueIndicator":self.trueIndicator,
        })

    
    def printAttributes(self):

        if(self.preferedValues != None):
            printablePrefArr=[]
            for condition in self.preferedValues["conditions"]:
                printablePrefArr.append({"condition":condition["condition"].__str__(), "isParentApplicable": condition["isParentApplicable"]})
            

        if(self.possibleValues != None):
            printablePossibleArr=[]
            for condition in self.possibleValues["conditions"]:
                printablePossibleArr.append({"condition":condition["condition"].__str__(), "isParentApplicable": condition["isParentApplicable"]})
        

        
        pp = pprint.PrettyPrinter(indent=4)
        pp.pprint({
            "var":self.var,
            "varType":self.varType,
            "globalInfo":self.globalInfo,
            "stackLocation":self.stackLocation,
            "preferedValues":{"prefArr":self.preferedValues["prefArr"],"conditions":printablePrefArr} if self.preferedValues!=None else None,
            "preferedChanche":self.preferedChanche,
            "possibleValues":{"prefArr":self.possibleValues["prefArr"],"conditions":printablePossibleArr} if self.possibleValues!=None else None,
            "backtrace":self.backtrace,
            "operation":self.operation,
            "structBegin":self.structBegin,
            "structEnd":self.structEnd,
            "trueIndicator":self.trueIndicator
        })

    def addPrefValByStackType(self, pref_info):
            if(not self.preferedValues):
                return

            if not self.varType in pref_info:
                pref_info[self.varType]=[]
            
            pref_info[self.varType].append({"stackLocation":self.stackLocation,"var":self.var,"prefArr":self.preferedValues["prefArr"],"conditions":self.preferedValues["conditions"] })


    def addPossibleValByStackType(self, possible_info):            
            if(not self.possibleValues):
                return

            if not self.varType in possible_info:
                possible_info[self.varType]=[]
            
            possible_info[self.varType].append({"stackLocation":self.stackLocation,"var":self.var,"prefArr":self.possibleValues["prefArr"],"conditions":self.possibleValues["conditions"] })


    def addPrefChanceByStackType(self, prefChance_info):
            if(not self.preferedChanche):
                return

            if not self.varType in prefChance_info:
                prefChance_info[self.varType]=[]

            if type(self.preferedChanche)==type([]):
                for prefChanche in self.preferedChanche:
                    prefChance_info[self.varType].append({"stackLocation":self.stackLocation,"var":self.var,"prefChance":prefChanche["prefChance"],"conditions":prefChanche["conditions"] })
            else:
                prefChance_info[self.varType].append({"stackLocation":self.stackLocation,"var":self.var,"prefChance":self.preferedChanche["prefChance"],"conditions":self.preferedChanche["conditions"] })


