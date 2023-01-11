
import pprint
from typing import Optional, TextIO, Dict, List
from isla_converter.parse_isla import ISLa_Parser
from isla_converter.functions_for_constraint_creation import paddSpezRule
from global_defines import GlobalDefines



class UniversalIslaConverter():
    def __init__(self, isla_file: Optional[TextIO],grammar:Dict[str, List[str]],universalLexer):
        self.isla_file = isla_file
        self.grammar=self.padGrammar(grammar, universalLexer)
        self.universalLexer=universalLexer

    def padGrammar(self, grammar, lexer):
        paddedGrammar={}
        for key, rules in grammar.items():
            paddedRules=[]
            for rule in rules:
                paddedRules.append(paddSpezRule(rule,lexer))
            paddedGrammar[key]=paddedRules
        return paddedGrammar


    def getConstraintInfo(self)->Dict[str, Dict[str,List[str]]] :
        originalNameList={}
        for item in self.grammar:
            originalNameList[GlobalDefines.normalize(item,GlobalDefines.NON_TERMINAL)]=item
            

        #print("1) read in the ISLA file and put it into quantorExpression format")
        quantorExpressions=ISLa_Parser(self.isla_file.read(),self.grammar).parse()
        #print(quantorExpressions)

        if(quantorExpressions==[]):
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

            return {
            "globalInfo":[stack,debugFunction],
            },{},originalNameList
        
        fullQuantorsExpression=[]
        
        for quantorExpression in quantorExpressions:
            #print("2) transform quantor expression to constraint")
            fullQuantorExpression=quantorExpression.getFullQuantorExpression(self.grammar, self.universalLexer)
            #for quantExpr in fullQuantorExpression:
            #    quantExpr.printAttributes()
            #raise ValueError("transform quantor expression to constraint")


            #print("3) handle backTrace")
            quantorExpression.handleBacktrace(fullQuantorExpression,self.grammar, self.universalLexer)
            #for quantExpr in fullQuantorExpression:
            #    quantExpr.printAttributes()
            #raise ValueError("after handle backtrace")
        
            #print("4) kreiere anweisungen für andere nonterminal, die sich durch prefered/possible ergeben und spez dafür")
            quantorExpression.createParentInfo(self.grammar, fullQuantorExpression)
            fullQuantorsExpression=fullQuantorsExpression+fullQuantorExpression
        #for quantExpr in fullQuantorsExpression:
        #    quantExpr.printAttributes()
        #raise ValueError("multiple sub constraint info")
        



        #print("5) get used derivation rules")
        spezRules={}
        quantorExpression.getSpezToAdd(fullQuantorsExpression,spezRules, self.universalLexer)

        #print("6) bringe constraints in eine lib form, sodass sie gut im weiteren schritt verarveitet werden können")
        libForm_quantorExpression=quantorExpression.getLibForm_Expression(fullQuantorsExpression,self.grammar)
        #pprint.pprint(libForm_quantorExpression)
        #raise ValueError("libForm_quantorExpression")

        return libForm_quantorExpression,spezRules, originalNameList
