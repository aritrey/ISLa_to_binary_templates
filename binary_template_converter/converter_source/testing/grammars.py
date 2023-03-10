

SCRIPT_SIZE_C={
    "<start>": ["<statement>"],
    "<statement>": [
        "<block>",
        "if    <paren_expr>      <statement> else <statement>",
        "while <paren_expr>      <statement>",
        "do    <statement> while<paren_expr>;     ",
        "<assignment>",
        ";     "
    ],

    
    "<block>": ["{     <statements>}     "],
    "<statements>": ["<block_statement><statements>", ""],
    "<block_statement>": ["<statement>", "<declaration>"],
    "<declaration>": [
        "int   <id><declaration'>;     "
    ],
    "<declaration'>": [
        "",
        "=     <expr>"
    ],
    "<assignment>": [
        "<id> =    <expr>;     "
    ],
    "<expr>": ["<test>"],
    "<test>": ["<add><test'>"],
    "<test'>": [
        "",
        "<     <add>"
    ],
    "<add>": ["<mul><add'>"],
    "<add'>": [
        "",
        "+     <mul><add'>",
        "-     <mul><add'>"
    ],
    "<mul>": ["<term><mul'>"],
    "<mul'>": [
        "",
        "*     <term><mul'>",
        "/     <term><mul'>"
    ],
    "<term>": [
        "<num>",
        "<id>",
        "<paren_expr>"
    ],
    "<paren_expr>": [
        "(     <test>)     "
    ],
    "<id>":[
        "a     ", 
        "b     ", 
        "c     ", 
        "d     ", 
        "e     ", 
        "f     ", 
        "g     ", 
        "h     ", 
        "i     ", 
        "j     ", 
        "k     ", 
        "l     ", 
        "m     ", 
        "n     ", 
        "o     ", 
        "p     ", 
        "q     ", 
        "r     ", 
        "s     ", 
        "t     ", 
        "u     ", 
        "v     ", 
        "w     ", 
        "x     ", 
        "y     ", 
        "z     "
    ],
    "<num>": [
        "<digit_nonzero><digits>",
        "0     "
    ],
    "<digits>": [
        "<digit><digits>",
        ""
    ],
    "<digit>": [
        "0     ", 
        "1     ", 
        "2     ", 
        "3     ", 
        "4     ", 
        "5     ", 
        "6     ", 
        "7     ", 
        "8     ", 
        "9     "
    ],
    "<digit_nonzero>": [
        "1     ", 
        "2     ", 
        "3     ", 
        "4     ", 
        "5     ", 
        "6     ", 
        "7     ", 
        "8     ", 
        "9     "
    ]
}

SIMPLE_LANG={
    "<start>": [
      "<E>$"
    ],
	"<E>": [
		"<T><EE>"
	],
	"<EE>": [
		"+<T><EE>",
		""
	],
	"<T>": [
		"<F><TT>"
	],
	"<TT>": [
		"*<F><TT>",
		""
	],
	"<F>": [
		"(<E>)",
		"a",
		"b",
		"c",
		"d",
		"e",
		"f",
		"g"
	]
}