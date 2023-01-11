from isla.isla_predicates import BEFORE_PREDICATE, IN_TREE_PREDICATE
from grammars import SCRIPT_SIZE_C
from test_functions import Tests


def test_script_size_c(testToken):


        no_redef_constr = """
    forall <statements> stmt1_1="int   {<id> id1_1}<declaration'>;     {<statements> parentStmt1}":
        forall <declaration> stmt2_1="int   {<id> id2_1}<declaration'>;     " in parentStmt1:
        (not (= id1_1 id2_1))"""

        def_use_inside_assgn_constr="""
    forall <assignment> assgn_2="{<id> id1_2} =    <expr>;     ":
        exists <statements> stmt2_2="int   {<id> id2_2}<declaration'>;     {<statements> stmt1_2}":
        (inside(assgn_2, stmt1_2) and (= id1_2 id2_2))"""

        def_use_before_term_constr= """
    forall <term> trm="{<id> id1}":
        exists <declaration> decl="int   {<id> id6}<declaration'>;     ":
        (before(decl, trm) and (= id1 id6))"""

        def_use=f"{def_use_inside_assgn_constr} and {def_use_before_term_constr}"
        def_use_and_no_redef=f"{def_use} and {no_redef_constr}"

        testInfo=[
            {
            "testname":"no_redef_constr",
            "constr":no_redef_constr,
            "predicates":set() 
            },
            {
            "testname":"def_use_inside_assgn_constr",
            "constr":def_use_inside_assgn_constr,
            "predicates":{IN_TREE_PREDICATE} 
            },
            {
            "testname":"def_use_before_term_constr",
            "constr":def_use_before_term_constr,
            "predicates":{BEFORE_PREDICATE} 
            },
            {
            "testname":"def_use",
            "constr":def_use,
            "predicates":{BEFORE_PREDICATE,IN_TREE_PREDICATE} 
            },
            {
            "testname":"def_use_and_no_redef",
            "constr":def_use_and_no_redef,
            "predicates":{BEFORE_PREDICATE,IN_TREE_PREDICATE} 
            },
        ]


        langageName="SCRIPT_SIZE_C"
        Tests(testInfo,SCRIPT_SIZE_C, langageName, testToken).run_tests()