

from typing import List
from global_defines import GlobalDefines


class Token():
    def __init__(self) -> None:
        pass
    def __str__(self):
        pass
    def setFalse(self):
        return None


##Datenstrukturen
#creates an array which stores both content and index for a nonterminal
# 
class StackValId(Token):
    """StackValId(name: str)
        creates an array which stores both content and index for a nonterminal. 
        name = Name of the created array
    """
    def __init__(self,name: str) -> None:
        self.name=name
    def __str__(self):
        return f"local string {self.name}[0];\nlocal int {self.name}Id[0];\nlocal int {self.name}Index=-1;\n"
    def getIndexAsString(self):
        return f"{self.name}Index"
    def getLengthAsString(self):
        return f"{self.name}Index + 1"

class VarBool(Token):
    def __init__(self,name) -> None:
        self.name=name
    def __str__(self):
        return f"local byte {self.name}=False;\n"

class VarVal(Token):
    def __init__(self,name) -> None:
        self.name=name
    def __str__(self):
        return f"local string {self.name}="";\n"

class ValAsStrgStack(Token):
    def __init__(self,name,val) -> None:
        self.name=name
        self.val=val
    def __str__(self):
        return f"local string {self.name}[]={{{self.val}}};\n"




#beschreibung von Variablen im File

class String_Token(Token):
    def __init__(self, str_var:str) -> None:
        self.str_var=str_var
    def __str__(self):
        return f'"{self.str_var}"'

class EOF(Token):
    def __init__(self) -> None:
        pass
    def __str__(self):
        return "<start>"

class This(Token):
    def __init__(self,var) -> None:
        self.var=var
    def __str__(self):
        return f"""selection"""

class ToValStack(Token):
    def __init__(self,name) -> None:
        self.name=name
    def __str__(self):
        return f"{self.name}"
    def getIndexAsString(self):
        return f"{self.name}Index"
    def getLengthAsString(self):
        return f"{self.name}Index + 1"

#string to stack
class ToStack(Token):
    def __init__(self,strg:str) -> None:
        self.strg=strg
    def __str__(self):
        return f"""{{{self.strg}}}"""
    def getIndexAsString(self):
        return f" 0 "
    def getLengthAsString(self):
        return f" 1 "

class ArrToStack(Token):
    def __init__(self,arr) -> None:
        self.arr=arr
    def __str__(self):

        arr=', '.join(f'"{w}"' for w in self.arr)
        return f"""{{{arr}}}"""
    def getIndexAsString(self):
        return f" {len(self.arr)-1} "
    def getLengthAsString(self):
        return f" {len(self.arr)} "





    
class StackLocation(Token):
    def __init__(self,stackLocationName) -> None:
        self.stackLocationName=stackLocationName
    def __str__(self):
        return self.stackLocationName

class StackLocationArr():
    def __init__(self,var,stackLocationArr) -> None:
        self.var=var
        try:
            if(type(stackLocationArr[0])!=type([])):
                self.stackLocationArr=[stackLocationArr]
            else:
                self.stackLocationArr=stackLocationArr
        except:
            raise ValueError("please proof your ISLa constraint for correctness of used grammar parts")

    def generateStackLocationIsValidString(self):
            
        stackLocationChecksString=""
        
        for stackLocation in self.stackLocationArr:
            stackLocationName=self.generateStackLocationName(stackLocation)
            stackLocationCheck=self.generateStackLocationCheckName(stackLocation)
            newStackLocationStringPart=', '.join(f'"{w}"' for w in stackLocation)
            stackLocationChecksString+=f"""
    local string {stackLocationName}[] = {{{newStackLocationStringPart}}};
    local byte {stackLocationCheck} = isSpecificPosition({stackLocationName},{ len(stackLocation) }, nontermStackIndex);"""
        return stackLocationChecksString

    def generateStackLocationName(self, stackLocation):
        return f"{self.var}_{GlobalDefines.normalize(''.join(stackLocation), GlobalDefines.ISLA_RULE)}"
    def generateStackLocationCheckName(self, stackLocation):
        return f"is_{self.generateStackLocationName(stackLocation)}"
    def generateStackLocationConditionToken(self):
        locations=None
        #add all possible locations
        for location in self.stackLocationArr:
            locations=Or(locations,StackLocation(self.generateStackLocationCheckName(location)))
        return locations

class CreatePrefPossibleArray(Token):
    def __init__(self,name, content:Token) -> None:
        self.name=name
        self.content=content
    def __str__(self):
        return f"""
local string {self.name}[]={self.content};
local int {self.name}Index={self.content.getIndexAsString()};
"""

class GetIdsOfStackLocBeginAndCreateStackLoc(Token):
    def __init__(self,stackLocations:List[ArrToStack],stackLocName) -> None:
        self.stackLocations=stackLocations
        self.stackLocName=stackLocName
    def __str__(self):
        returnStr=""
        for stackLoc in self.stackLocations:
            stackLocationName=self.stackLocName
            returnStr+= f"""
local string {stackLocationName}[] = {stackLoc};
local int {stackLocationName}Index = {stackLoc.getIndexAsString()};
local int idsOfStackLocBegin[0];
local int idsOfStackLocBeginIndex=-1;
local int index=getIndexOfSpecificPosition({stackLocationName}, {stackLocationName}Index+1, nontermStackIndex);
if(index!=-1){{
    idsOfStackLocBegin+=nontermStackId[index];
    idsOfStackLocBeginIndex=idsOfStackLocBeginIndex+1;
}}
"""
        return returnStr






#__________pref/possible#kreiert Pref/Possible Val  -> eig was anderes

class NotEquals_WithStack(Token):
    def __init__(self,stackName) -> None:
        self.stackName=stackName
    def __str__(self):
        return f"""{self.stackName}"""
    def getIndexAsString(self):
        return f""" possible_val_helpIndex-{self.stackName}Index+1 """

class PossibleNotFound(Token):
    def __init__(self) -> None:
        pass
    def __str__(self):
        return """
if (epsilon1) {
    possible_val_Index = mergeLists(possible_val_help, possible_val_helpIndex, follow, size-1, possible_val);
} else {
    possible_val_Index = addList(possible_val_help, possible_val_helpIndex, possible_val, possible_val_Index);
}
"""

class PrefNotFound(Token):
    def __init__(self) -> None:
        pass
    def __str__(self):
        return """
pref_val_Index = addList(possible_val, possible_val_Index, pref_val, pref_val_Index);
"""

class NoPrefChanceDeclared(Token):
    def __init__(self) -> None:
        pass
    def __str__(self):
        return f"""
local int pref_possibility={GlobalDefines.STANDARD_PREF_POSSIBILITY};
"""

class Possible(Token):
    def __init__(self,value:Token) -> None:
        self.value=value
    def __str__(self):
        possibleValHelpName=f"{GlobalDefines.normalize('possible_val_help', GlobalDefines.ISLA_RULE)}"
        additional=""
        isNewArray=type(self.value)==ToStack or type(self.value)==ArrToStack
        arrayAlreadyExists=type(self.value)==StackValId or type(self.value)==ToValStack
        notEqualsWithStack=type(self.value)==NotEquals_WithStack
        list_len=self.value.getIndexAsString()
        if(not isNewArray and not arrayAlreadyExists and not notEqualsWithStack):
            strInfo=f"type in prefered is: {type(self.value)}"
            raise ValueError(f"Not implemented {strInfo}")
        if(isNewArray):
            additional=f"local string {possibleValHelpName}[] = {self.value};"
        if(notEqualsWithStack):
            list_len=f"{possibleValHelpName}_ll"
            additional=f"""
                    local string {possibleValHelpName}[0];
                    local int {possibleValHelpName}Index=-1;
                    if (epsilon1) {{
                        {possibleValHelpName}Index = mergeLists(possible_val_help, possible_val_helpIndex, follow, size-1, {possibleValHelpName});
                    }} else {{
                        {possibleValHelpName}Index = addList(possible_val_help, possible_val_helpIndex, {possibleValHelpName}, {possibleValHelpName}Index);
                    }}
                    local int {possibleValHelpName}_ll=getUnequalWithStack({possibleValHelpName},{possibleValHelpName}Index, {self.value.__str__()}, {self.value.__str__()}Index);
            """
        if(arrayAlreadyExists):
            possibleValHelpName=self.value

        return f"""
{additional}
possible_val_Index = addList({possibleValHelpName}, {list_len}, possible_val, possible_val_Index);
"""
    def executedByParent(self, info):
        pass

class Prefered(Token):
    def __init__(self,value:Token) -> None:
        self.value=value
    def __str__(self):
        prefValHelpName=f"{GlobalDefines.normalize('pref_val_help', GlobalDefines.ISLA_RULE)}"
        additional=""
        list_name=self.value.getIndexAsString()
        isNewArray=type(self.value)==ToStack or type(self.value)==ArrToStack
        arrayAlreadyExists=type(self.value)==StackValId or type(self.value)==ToValStack
        notEqualsWithStack=type(self.value)==NotEquals_WithStack
        if(not isNewArray and not arrayAlreadyExists and not notEqualsWithStack):
            strInfo=f"type in prefered is: {type(self.value)}"
            raise ValueError(f"{strInfo} not suported")
        if(isNewArray):
            additional=f"local string {prefValHelpName}[] = {self.value};"
        if(notEqualsWithStack):
            list_name=f"{prefValHelpName}_ll"
            additional=f"""
                    local string {prefValHelpName}[0];
                    local int {prefValHelpName}Index=-1;
                    if (epsilon1) {{
                        {prefValHelpName}Index = mergeLists(possible_val_help, possible_val_helpIndex, follow, size-1, {prefValHelpName});
                    }} else {{
                        {prefValHelpName}Index = addList(possible_val_help, possible_val_helpIndex, {prefValHelpName}, {prefValHelpName}Index);
                    }}
                    local int {prefValHelpName}_ll=getUnequalWithStack({prefValHelpName},{prefValHelpName}Index, {self.value.__str__()}, {self.value.__str__()}Index);
            """
        if(arrayAlreadyExists):
            prefValHelpName=self.value


        return f"""
{additional}
pref_val_Index = addList({prefValHelpName}, {list_name},pref_val,pref_val_Index);
        """
    def executedByParent(self, info):
        pass

class PrefChance(Token):
    def __init__(self,value:float) -> None:
        self.value=value
    def __str__(self):
        return f"""
pref_possibility = {self.value};
"""
    def divideBy2(self):
        self.value=self.value/2

    def getValue(self):
        return self.value   

class AddToPrefPossibleIfValInStack(Token):
    def __init__(self,stackListsList,commonValWithoutCurrSets:set,isPref:bool) -> None:
        self.stackListsList=stackListsList
        self.commonValWithoutCurrSets=commonValWithoutCurrSets
        self.isPref=isPref
    def normalizeConjNameByIndex(self, index):
        return f"conjunction_{index}_stack"
    def normalizeDisjNameByIndex(self, index):
        return f"disjunction_{index}_stack"

    def __str__(self):
        if(len(self.stackListsList)==1 and not bool(self.commonValWithoutCurrSets)):#nur conjunction
            returnVal=None
            for stack in self.stackListsList[0]["stackList"]:
                addToPrefPossible= Prefered(ToValStack(stack)) if self.isPref else Possible(ToValStack(stack))
                returnVal=SequentialExecution(returnVal, addToPrefPossible)
            for stack in self.stackListsList[0]["avoidList"]:
                addToPrefPossible= Prefered(NotEquals_WithStack(stack)) if self.isPref else Possible(NotEquals_WithStack(stack))
                returnVal=SequentialExecution(returnVal, addToPrefPossible)
            
            return f"{returnVal}" if returnVal else None


        #handle stackListsList
        currListName=GlobalDefines.normalize('valToAdd', GlobalDefines.ISLA_RULE)
        strg=""
        if(self.commonValWithoutCurrSets):
            strg+=CreatePrefPossibleArray(currListName, ArrToStack(self.commonValWithoutCurrSets)).__str__()
        else:
            strg+=f"local string {currListName}[0];\n local int {currListName}Index=-1;\n"        

        for index,lst in enumerate(self.stackListsList):#{"stackList":[...],"avoidList":[...]}
            #currListName=self.normalizeConjNameByIndex(index)
            
            #handle disjunktion
            
            currDisjListName=""
            if(len(lst["stackList"])==1 and len(lst["avoidList"])==0):
                currDisjListName=lst["stackList"][0]
            else:
                currDisjListName=self.normalizeDisjNameByIndex(index)
                strg+=f"local string {currDisjListName}[0];\n local int {currDisjListName}Index=-1;\n"
                
                for stack in lst["stackList"]:
                    strg+=f"{currDisjListName}Index = addList({stack},{stack}Index+1,{currDisjListName}, {currDisjListName}Index);\n"
                for stack in lst["avoidList"]:
                    possibleValHelpName=GlobalDefines.normalize(currDisjListName, GlobalDefines.ISLA_RULE)
                    strg+=f"""
                    local string {possibleValHelpName}[0];
                    local int {possibleValHelpName}Index=-1;
                    if (epsilon1) {{
                        {possibleValHelpName}Index = mergeLists(possible_val_help, possible_val_helpIndex, follow, size-1, {possibleValHelpName});
                    }} else {{
                        {possibleValHelpName}Index = addList(possible_val_help, possible_val_helpIndex, {possibleValHelpName}, {possibleValHelpName}Index);
                    }}
                    {possibleValHelpName}Index = getUnequalWithStack({possibleValHelpName},{possibleValHelpName}Index, {stack}, {stack}Index);
                    {currDisjListName}Index = addList({possibleValHelpName},{possibleValHelpName}Index,{currDisjListName}, {currDisjListName}Index);\n
                    """
                
            if(index==0 and not self.commonValWithoutCurrSets):
                strg+=f"{currListName}Index = addList({currDisjListName},{currDisjListName}Index,{currListName}, {currListName}Index);\n"
            else:
                strg+=f"{currListName}Index = createConjunctionOfLists({currDisjListName},{currDisjListName}Index,{currListName}, {currListName}Index);\n"

        addToPrefPossible= Prefered(ToValStack(currListName)) if self.isPref else Possible(ToValStack(currListName))
        return  strg+ addToPrefPossible.__str__()

    def addVal(self, var):
        self.var=ToValStack(var)






##Operationen
class Assign(Token):
    def __init__(self,var1,var2) -> None:
        self.var1=var1
        self.var2=var2
    def __str__(self):
        return f"{self.var1}={self.var2};\n"

#used for getSeenInfo-> da wird zuerst ein array erstellt und das dann ausgeführt
class SequentialExecution(Token):
    def __init__(self,token1,token2) -> None:
        self.token1=token1
        self.token2=token2
    def __str__(self):
        if(self.token1 and self.token2):
            return f"""
{self.token1}
{self.token2}
"""
        elif(self.token1):
            return f"{self.token1}"
        elif(self.token2):
            return f"{self.token2}"
        else:
            raise ValueError("no val for sequential execution specified")


    def getIndexAsString(self):
        return self.token2.getIndexAsString()
    def getLengthAsString(self):
        return self.token2.getLengthAsString()
    def executedByParent(self, normalFirst):
        #self.token1.executedByParent(normalFirst)
        self.token2.executedByParent(normalFirst)

class AddToStackWithId(Token):
    def __init__(self,stackName,value:Token) -> None:
        self.stackName=stackName
        self.value=value
    def __str__(self):
        return f"""
	{self.stackName}+={self.value};
	{self.stackName}Id+=currNontermStackIndex;
	{self.stackName}Index={self.stackName}Index+1;"""

class RemoveFromStackWithVal(Token):
    def __init__(self,stackName,condition) -> None:
        self.stackName=stackName
        self.condition=condition
    def __str__(self):
        condition=self.condition if self.condition else "isInStringArray(selection, {self.stackName}, {self.stackName}Index+1)"

        return f"""
        if({condition}){{
            local int removeLocation=findInStringArray(selection, {self.stackName}, {self.stackName}Index+1);
            {self.stackName}-={self.stackName}[removeLocation];
    		{self.stackName}Id-={self.stackName}Id[removeLocation];
            {self.stackName}Index={self.stackName}Index-1;
        }}"""

class RemoveFromStackWithId(Token):
    def __init__(self,stackName) -> None:
        self.stackName=stackName
    def __str__(self):
        return f"""
if(isInIntArray(currNontermStackIndex, {self.stackName}Id, {self.stackName}Index+1)){{
	local int removeLocation=findInIntArray(currNontermStackIndex, {self.stackName}Id, {self.stackName}Index+1);
    {self.stackName}-={self.stackName}[removeLocation];
    {self.stackName}Id-={self.stackName}Id[removeLocation];
	{self.stackName}Index={self.stackName}Index-1;
}}"""

class RemoveFromStackAsContainingNonterm(Token):
    def __init__(self,stackName, nonTermType) -> None:
        self.stackName=stackName
        self.nonTermType=nonTermType
    def __str__(self):
        return f"""
local int i;
for(i=currNontermStackIndex+1; i<=nontermStackIndex; i++){{
	if(nontermStack[i]==\"{self.nonTermType}\"){{
		if(isInIntArray(nontermStackId[i], {self.stackName}Id,{self.stackName}Index+1)){{
			local int removeLocation=findInIntArray(nontermStackId[i], {self.stackName}Id, {self.stackName}Index+1);
            {self.stackName}-={self.stackName}[removeLocation];
    		{self.stackName}Id-={self.stackName}Id[removeLocation];
			{self.stackName}Index={self.stackName}Index-1;
        }}
    }}
}}"""
class CopyToStackAsParent(Token):
    def __init__(self,stackNameOrigin, stackNameTarget,nonTermType) -> None:
        self.stackNameOrigin=stackNameOrigin
        self.stackNameTarget=stackNameTarget
        self.nonTermType=nonTermType
    def __str__(self):
        return f"""
local int i;
for(i=currNontermStackIndex; i<=nontermStackIndex; i++){{
	if(nontermStack[i]==\"{self.nonTermType}\"){{
        local int indexFound=findInIntArray( nontermStackId[i], {self.stackNameOrigin}Id,{self.stackNameOrigin}Index+1);
		if(indexFound>-1){{
			{self.stackNameTarget}+={self.stackNameOrigin}[indexFound];
    		{self.stackNameTarget}Id+={self.stackNameOrigin}Id[indexFound];
            {self.stackNameTarget}Index={self.stackNameTarget}Index+1;
        }}
    }}
}}
"""

class SearchInParentNonterm(Token):
    def __init__(self,childType,stackName,indicesFoundArrName="indicesFound") -> None:
        self.stackName=stackName
        self.childType=childType
        self.indicesFoundArrName=indicesFoundArrName
    def __str__(self):
        return f"""
local int i;
local int {self.indicesFoundArrName}[0];
local int {self.indicesFoundArrName}Index=-1;
for(i=currNontermStackIndex; i<=nontermStackIndex; i++){{
	if(nontermStack[i]==\"{self.childType}\"){{
		if(isInIntArray(nontermStackId[i], {self.stackName}Id,{self.stackName}Index+1)){{
			{self.indicesFoundArrName}+=i;
            {self.indicesFoundArrName}Index={self.indicesFoundArrName}Index+1;
        }}
    }}
}}
"""

class ForallValInStack(Token):
    def __init__(self,condition,stack,ifTrue,ifFalse) -> None:
        self.condition=condition
        self.stack=stack
        self.ifTrue=ifTrue
        self.ifFalse=ifFalse
    def __str__(self):
        self.condition.addVal(f"{self.stack}[i]")
        condition=Conditional(condition=IsTrue("isTrueForallStackVal"), ifTrue=self.ifTrue,ifFalse=self.ifFalse)
        return f"""
local byte isTrueForallStackVal=True;
local int i;
for(i=0; i<={self.stack}Index; i++){{
    if(!({self.condition})){{
        isTrueForallStackVal=False;
    }}
}}
{condition}
"""

class DoForallValInStack(Token):
    def __init__(self,condition,stack:str,ifTrue,ifFalse) -> None:
        self.condition=condition
        self.stack=stack
        self.ifTrue=ifTrue
        self.ifFalse=ifFalse
    def __str__(self):
        self.condition.addVal(f"{self.stack}[i]")
        elseCase=""
        if(self.ifFalse):
            elseCase=f"else{{\n{self.ifFalse}\n}}"
        
        return f"""
local int i;
for(i=0; i<={self.stack}Index; i++){{
    if({self.condition}){{
        {self.ifTrue}
    }}{elseCase}
}}
"""

class ParentExistsInStack(Token):
    def __init__(self,stack) -> None:
        self.stack=stack
    def __str__(self):
        return f" {self.stack}Index>=0 "

class ParentsRemoveFromStack(Token):
    def __init__(self,condition,stackName) -> None:
        self.condition=condition
        self.stackName=stackName
    def __str__(self):
        return f"""
        local int i;
        local int removedItemCount = 0;
        for(i={self.stackName}Index; i>=0; i--){{
            if({self.condition}){{
                removeFromStackByIndex(i, {self.stackName},{self.stackName}Id, {self.stackName}Index+1);
                removedItemCount=removedItemCount+1;
            }}
        }}
        {self.stackName}Index = {self.stackName}Index - removedItemCount;
"""

        


##Conditions
class Conditional(Token):
    def __init__(self,condition,ifTrue,ifFalse=None) -> None:
        self.condition=condition
        self.ifTrue=ifTrue
        self.ifFalse=ifFalse
    def getValue(self):
        return max(self.ifFalse.getValue(),self.ifTrue.getValue())   
    def executedByParent(self, normalFirst):
        self.ifTrue.executedByParent(normalFirst)
        self.ifFalse.executedByParent(normalFirst)
    def divideBy2(self):
        self.ifTrue.divideBy2()
        if(self.ifFalse!=None):
            self.ifFalse.divideBy2()
    def __str__(self):
        if(self.ifFalse!=None):
            return f"""
if({self.condition}){{
	{self.ifTrue}
}}else{{
	{self.ifFalse}
}}
"""
        else:
            return f"""
if({self.condition}){{
	{self.ifTrue}
}}
"""

class ExistsInStack(Token):
    def __init__(self,var:Token,stackName:Token) -> None:
        self.var=var
        self.stackName=stackName
    def __str__(self):
        stackNameStr=self.stackName
        return f" isInStringArray({self.var}, {stackNameStr}, {stackNameStr}Index+1) "
    def addVal(self, var):
        self.var=ToValStack(var)

class IsPossibleNotToHaveNonterm(Token):
    def __init__(self,insideOrAfter, parent, child) -> None:
        self.insideOrAfter=insideOrAfter
        self.parent=parent
        self.child=child


class And(Token):
    def __init__(self,condition1,condition2) -> None:
        self.condition1=condition1
        self.condition2=condition2
    def __str__(self):
        if(not self.condition2):
            return f"{self.condition1}"
        if(not self.condition1):
            return f"{self.condition2}"
        return f"""{self.condition1} && {self.condition2}"""

class Or(Token):
    def __init__(self,condition1,condition2) -> None:
        self.condition1=condition1
        self.condition2=condition2
    def __str__(self):
        if(not self.condition2):
            return f"{self.condition1}"
        if(not self.condition1):
            return f"{self.condition2}"
        return f"""({self.condition1} || {self.condition2})"""

class Equals(Token):
    def __init__(self,var1,var2=None) -> None:
        self.var1=var1
        self.var2=var2
    def __str__(self):
        if(self.var2==None):
            raise ValueError("var2 must be specified, (maybe not given value in ForallValInStack?)")
        return f"""{self.var1} == {self.var2}"""
    def addVal(self, var2):
        self.var2=var2

class StackEmpty(Token):
    def __init__(self,stackName) -> None:
        self.stackName=stackName
    def __str__(self):
        return f"""{self.stackName}Index==-1"""

class ExistDiffValInStack(Token):
    def __init__(self,stackName) -> None:
        self.stackName=stackName
    def __str__(self):
        return f""" existDiffValInStack( {self.stackName}, {self.stackName}Index+1) """

class Not(Token):
    def __init__(self,condition) -> None:
        self.condition=condition
    def __str__(self):
        return f"""!({self.condition})"""

class IsTrue(Token):
    def __init__(self,condition) -> None:
        self.condition=condition
    def __str__(self):
        return f"""True=={self.condition}"""
    def setFalse(self):
        return Assign(self.condition, False)

class IsFalse(Token):
    def __init__(self,condition) -> None:
        self.condition=condition
    def __str__(self):
        return f"""False=={self.condition}"""
    def setFalse(self):
        return Assign(self.condition, True)





##backtrace

class Avoid(Token):
    def __init__(self,locationToAvoid, condition) -> None:
        self.locationToAvoid=locationToAvoid
        self.condition=condition

class Seen(Token):
    def __init__(self,globalSeenIndicator, until, derivationRulesToUse, flagForLast,valueToSee,doWithLastValue=None, parentStack=[]) -> None:
        self.globalSeenIndicator=globalSeenIndicator
        self.until=until
        self.derivationRulesToUse=derivationRulesToUse
        self.flagForLast=flagForLast
        self.doWithLastValue=doWithLastValue
        self.valueToSee=valueToSee
        self.parentStack=parentStack


class NontermSeen(Token):
    def __init__(self,globalSeenIndicator, until, derivationRulesToUse, flagForLast,notSeenCondition) -> None:
        self.globalSeenIndicator=globalSeenIndicator
        self.until=until
        self.derivationRulesToUse=derivationRulesToUse
        self.flagForLast=flagForLast
        self.notSeenCondition=notSeenCondition



class StructuralRelation():
    def __init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar,reversed):
        self.var1=var1
        self.var2=var2
        self.var1QuantorInvolved=var1QuantorInvolved
        self.var2QuantorInvolved=var2QuantorInvolved
        self.commonParentConstrNr=commonParentConstrNr
        self.commonParentConstrVar=commonParentConstrVar
        self.reversed=reversed
    def isInCurrentConstraint(self, smallestConstraintNr):
        var12Involved=self.var1QuantorInvolved>=smallestConstraintNr and self.var2QuantorInvolved>=smallestConstraintNr
        var22InCurrExpr=self.var1QuantorInvolved==smallestConstraintNr or self.var2QuantorInvolved==smallestConstraintNr 
        return var12Involved and var22InCurrExpr
    def print(self):
        print("var1: ",self.var1)
        print("var2: ",self.var2)
        print("var1QuantorInvolved: ",self.var1QuantorInvolved)
        print("var2QuantorInvolved: ",self.var2QuantorInvolved)
        print("isReverseRelation: ",self.isReverseRelation())
    def isCommonParentConstrNr(self, constraintNr):
        return self.commonParentConstrNr == constraintNr
    def getVarUpper(self):
        if(self.var1QuantorInvolved<self.var2QuantorInvolved):
            return self.var1
        else:
            return self.var2
    def getVarDowner(self):
        if(self.var1QuantorInvolved>self.var2QuantorInvolved):
            return self.var1
        else:
            return self.var2
    def getUpperElem(self):
        return self.commonParentConstrVar    
    def isReverseRelation(self):
        return self.reversed

#var1 inside var2
class Inside(StructuralRelation):
    def __init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar,reversed):
        StructuralRelation.__init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar,reversed)


class Wellformed(StructuralRelation):
    def __init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar,reversed):
        StructuralRelation.__init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved, commonParentConstrNr,commonParentConstrVar,reversed)
    def isReverseRelation(self):
        return False

class Before(StructuralRelation):
    def __init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved,commonParentConstrNr,commonParentConstrVar,reversed):
        StructuralRelation.__init__(self,var1,var2,var1QuantorInvolved,var2QuantorInvolved, commonParentConstrNr,commonParentConstrVar,reversed)


