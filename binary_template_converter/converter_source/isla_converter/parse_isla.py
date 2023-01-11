
import re
from pyparsing import srange
from isla.derivation_tree import DerivationTree
from isla.parser import EarleyParser
from isla.language import parse_isla
from isla.isla_predicates import BEFORE_PREDICATE, IN_TREE_PREDICATE
from isla_converter.quantor_expression import QuantorExpression

class ISLa_Parser():
    def __init__(self,unparsed_constr:str,grammar) -> None:
        self.unparsed_constr=unparsed_constr
        self.grammar=grammar

    def extractString(self, tree, index, numberToCompare,correctionVal):
        extracted=""
        next_leave=next(tree)
        while(next_leave[0][index]==numberToCompare+correctionVal):
            extracted+=str((next_leave[1]))
            next_leave=next(tree)
            try:
                next_leave[0][index]
            except:
                break
        return extracted

    def  handleCondition(self, tree, index):
        inside_or_before=None
        var1=None 
        var2=None
        var3=None 
        var4=None
        arithConstr=None
        #handle condition condition:
        next_leave=str(next(tree)[1])
        if(next_leave=="(("):#multiple constr
            next_leave=str(next(tree)[1])
            if(next_leave=="before" or next_leave=="inside"):
                inside_or_before=next_leave
                next(tree)#(
                var3=self.extractString(tree, index+2, 2,0)#+ ", "
                var4=self.extractString(tree, index+2, 4,0)#+ ")"
                next(tree)# ∧ 
                next_leave=str(next(tree)[1])
                if(next_leave=="Not("):#not var1==var2
                    arithConstr="!="
                    var1=self.extractString(tree, index+3, 0,0)#+" == "
                    var2=self.extractString(tree, index+3, 2,0)#+ ")"
                    next(tree)#)) 
                    next(tree)#)-> arithmetik ende
                else:#var1==var2 
                    arithConstr="="
                    var1=next_leave+self.extractString(tree, index+3, 0,0)#+" == "
                    var2=self.extractString(tree, index+3, 2,0)#+ "))" 
                    next(tree)#)-> arithmetik ende

            else:
                if(next_leave=="Not("):#not var1==var2
                    arithConstr="!="
                    var1=self.extractString(tree, index+3, 0,0)#+ ", "
                    var2=self.extractString(tree, index+3, 2,0)#+ ")"
                    next(tree)#+ " ∧ "
                else:#var1==var2 
                    arithConstr="="
                    var1=next_leave+self.extractString(tree, index+3, 0,0)#+ " == "
                    var2=self.extractString(tree, index+3, 2,0)#+ " AND "

                inside_or_before=str(next(tree)[1])
                next(tree)#(
                var3=self.extractString(tree, index+2, 2,0)#+ ", "
                var4=self.extractString(tree, index+2, 4,0)#+ ")"
                next(tree)#))


        else:#(
            next_leave=str(next(tree)[1])
            if(next_leave=="Not("):#not var1==var2
                arithConstr="!="
                var1=self.extractString(tree, index+4, 0,0)#+ ", "
                var2=self.extractString(tree, index+4, 2,0)#+ ")"
                next(tree)#)
                next(tree)#)
            else:#var1==var2 
                arithConstr="="
                var1=next_leave+self.extractString(tree, index+4, 0,0)#+ " == "
                var2=self.extractString(tree, index+4, 2,0)#+ ")"
                next(tree)#)

        return var1, var2, arithConstr, var3, var4, inside_or_before

            
    def getVarName(self,elemName, quantor):  
        quantor_str="forall" if quantor=="∀" else "exists"
        searchstr=f"{quantor_str}[ ]*(<[a-zA-Z0-9'_-]+>)[ ]*{elemName}"
        result = re.search(searchstr, self.unparsed_constr)
        return result.group(1)



    def check_if_grammar_can_be_processed(self, ISL_constr):
        processableGrammar={"<start>":["<quantor_exprs>"],
        "<quantor_exprs>":["<quantor_expr>", "(<quantor_exprs> ∧ <quantor_expr>)"],
        "<quantor_expr>":["<quantor><opt_spez> <var> ∈ <var>: (<quantor><opt_spez> <var> ∈ <var>: <constr>)"],
        "<opt_spez>":[ " <quote><spez><quote> =",""],
        "<quote>":['"',"\'"],
        "<var>":["<chars>"],
        "<var_or_str>":["<chars>","'<chars>'",'"<chars>"'],
        "<chars>":["<char><chars>","<char>"],
        "<char>":srange("[A-Za-z0-9_-]"),
        "<spez_char>":srange("[\000-\377]"),
        "<spez>":["<spez_char><spez>","<spez_char>"],
        "<quantor>":["∀","∃"],
        "<constr>":["((<structral_constr> ∧ <arith_constr>))","((<arith_constr> ∧ <structral_constr>))","<arith_constr_alone>"],
        "<structral_constr>":["<structure_str>(<var>, <var>)"],
        "<structure_str>":["before","inside"],
        "<arith_constr_alone>":["(<arith_constr>)"],
        "<arith_constr>":["<equal_str>", "Not(<equal_str>)"],
        "<equal_str>":["<var_or_str> == <var_or_str>"],}

        try:
            w_tree = DerivationTree.from_parse_tree(next(EarleyParser(processableGrammar).parse(ISL_constr)))
            return w_tree.leaves()
        except:
            raise ValueError("isla constraint can not be barsed by this tool. Please try another constraint")
        

    def parse(self):
        ISL_constr=str(parse_isla(self.unparsed_constr, self.grammar, {BEFORE_PREDICATE,IN_TREE_PREDICATE}))

        tree=self.check_if_grammar_can_be_processed(ISL_constr)
        next_leave=str(next(tree)[1])
        numberOfParenthesis=0
        constrArr=[]
        while(next_leave=="("):
            numberOfParenthesis+=1
            next_leave=str(next(tree)[1])
        iterations=2+numberOfParenthesis
        for index in range(iterations,1,-1):
            correctionVal=0
            quantor1=next_leave#quantor
            spez1=None
            if(next(tree)[1].value!='<opt_spez>'):
                str(next(tree)[1])#"
                #handle natch expression and closing "
                spez1=self.extractString(tree, index+1, 2,correctionVal)
                next(tree)#=
            next(tree)#" "
            #handle quantified variable name and quantified variable
            varName1=self.extractString(tree, index, 3,correctionVal)
            #handle inside and ( 
            containing1=self.extractString(tree, index, 5,correctionVal)
            quantor2=str(next(tree)[1])#second quantifier
            spez2=None
            if (next(tree)[1].value!='<opt_spez>'):
                #handle natch expression and closing "
                next(tree)#" "
                spez2=self.extractString(tree, index+1, 2,correctionVal)
                next(tree)#" ="
            next(tree)#" ""
            
            varName2=self.extractString(tree, index, 10,correctionVal)
            #handle inside:
            containing2=self.extractString(tree, index, 12,correctionVal)
            var1, var2, arithExpr , var3, var4, inside_or_before = self.handleCondition(tree, index)
            if(index>2):
                next(tree)#") "
                if(numberOfParenthesis>1 and index<iterations):#:_MARK
                    next(tree)#" ∧ "
                next_leave=str((next(tree)[1]))#quantor
            
            parentVar1=self.getVarName(varName1, quantor1)
            parentVar2=self.getVarName(varName2, quantor2)
            upperExpr=QuantorExpression(0,None,quantor1,parentVar1,varName1,spez1,containing1,None,None,None,None)
            downerExpr=QuantorExpression(1,upperExpr,quantor2,parentVar2,varName2,spez2,containing2,var1,var2,arithExpr,"and" if var3 else None)
            if(var3):
                downerExpr=QuantorExpression(2,downerExpr,None,None,None,None,"start",var3,var4,inside_or_before, None)
            constrArr.append(downerExpr)
        return constrArr