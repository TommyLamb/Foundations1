datatype BEXP = BAPP of BEXP * BEXP
       | BLAM of BEXP
       | BID of int;
	   
datatype COM = CAPP of COM*COM
       | CID of string
       | CI
       | CK
       | CS;
	   
datatype IEXP = IAPP of IEXP * IEXP
       | ILAM of string * IEXP
       | IID of string;
	   
datatype IBEXP = IBAPP of IBEXP * IBEXP
       | IBLAM of IBEXP
       | IBID of int;

datatype LEXP = APP of LEXP * LEXP
       | LAM of string * LEXP
       | ID of string;
	   
use "Bruijn.sml";
use "Combinatorics.sml";
use "Item.sml";
use "ItemBruijn.sml";
use "Lambda.sml";