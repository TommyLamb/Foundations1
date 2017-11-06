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

(*############ Combinator Functions ############*)
structure Combinators = struct

fun printEXP (CID v) = print v
  | printEXP (CI) = print "I''"
  | printEXP (CS) = print "S''"
  | printEXP (CK) = print "K''"
  | printEXP (CAPP (a, b)) = (
	print "("; 
	printEXP a;
	printEXP b;
	print ")"
	);

fun isRedex (CAPP (CI, v)) = true
  | isRedex (CAPP ((CAPP (CK, v1)), v2)) = true 
  | isRedex (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = true
  | isRedex _ = false;

fun hasRedex (CAPP (x, y)) = (isRedex (CAPP (x, y))) orelse hasRedex x orelse hasRedex y 
  | hasRedex _ = false;

fun appToList expression [] = []
  | appToList expression (hd::tl) = (CAPP (expression, hd))::(appToList expression tl);

fun appFromList [] expression = []
  | appFromList (hd::tl) expression = (CAPP (hd, expression))::(appFromList tl expression);

fun red (CAPP (CI, v)) = v
  | red (CAPP ((CAPP (CK, v1)), v2)) = v1 
  | red (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = CAPP ((CAPP ( v1, v3)), (CAPP ( v2, v3)));

  (* For comments see Lamda.leftmost *)
fun reduce (CID v) = [CID v]
  | reduce (CI) = [CI]
  | reduce (CK) = [CK]
  | reduce (CS) = [CS]
  | reduce (CAPP (a, b)) = 
	if (isRedex (CAPP(a, b))) then
		(CAPP(a, b))::(reduce (red (CAPP(a, b))))
	else if (isRedex a) then
		(CAPP(a, b))::(reduce (CAPP ((red a), b)))
	else if (isRedex b) then	
		(CAPP(a, b))::(reduce (CAPP (a, (red b))))
	else if (hasRedex a) then
		let 
			val abreduction = (appFromList (reduce a) b)
		in
			abreduction@(tl (reduce (List.last abreduction)))
		end
	else if (hasRedex b) then
		appToList a (reduce b)
	else
		[CAPP (a, b)];
  

		
fun printReduction [] = print "\n"
  | printReduction (hd::[]) = (printEXP hd; print "\n")
  | printReduction (hd::tl) = (printEXP hd; print " -->\n"; printReduction tl);
  

fun printReductionCount x = (
		printReduction x;
		print "Steps: ";
		print (Int.toString((List.length x)-1));
		print "\n"
		);
  
fun subtermsList (CID v) = [CID v]
  | subtermsList (CI) = [CI]
  | subtermsList (CK) = [CK]
  | subtermsList (CS) = [CS]
  | subtermsList (CAPP (a, b)) = [CAPP (a, b)]@(subtermsList a)@(subtermsList b);

  
fun setify [] = []
  | setify (hd::tl) = 
	if (List.exists (fn x => hd = x) tl) then
		setify tl
	else
		hd::setify tl;

fun subterms x = setify (subtermsList x);

(* Note that SML will type this COM -> COM -> bool, even if every clause was (CID id) (COM). Thus it whines about
non exhaustive matches without the wildcard clause *)
fun free (CID id) (CID x) = (id = x)
  | free (CID id) (CAPP (a, b)) = (free (CID id) a) orelse (free (CID id) b) 
  | free _ _ = false;


val red3 =  (CAPP ((CAPP ((CAPP (CS, CID "v1")), CID "v2")), CID "v3"));


val vx = CID "x";
val vy = CID "y";
val vz = CID "z";

val t1 = CI;
val t2 = CAPP (CK, vx);
val t3 = CAPP (CAPP (CI, CAPP (CK, vx)), vz);
val t4 = CAPP (CI, vz);
val t5 = CAPP (CAPP (CAPP (CI, CAPP (CK, vx)), vz), CAPP (CAPP (CI, CAPP (CK, vx)), vz));
val t6 = CS;
val t7 = CAPP (CAPP (CS, CI), CI);
val t8 = CAPP (CAPP (CS, CI), CI);
val t9 = CAPP (CAPP (CAPP (CS, CI), CI), CAPP (CAPP (CI, CAPP (CK, vz)), vz));
val omega = CAPP (CAPP (CAPP (CS, CI), CI), CAPP (CAPP (CS, CI), CI));

val list = [vx, vy, vz, t1, t2, t3, t4, t5, t6, t7, t8, t9];

end


(*############ Lambda Functions ############*)
structure Lambda = struct

fun printEXP (ID v) = print v
  | printEXP (LAM (v,e)) =
		(print "(\206\187";
		print v;
		print ".";
		printEXP e;
		print ")")
  | printEXP (APP(e1,e2)) =
    (print "(";
     printEXP e1;
     print " ";
     printEXP e2;
     print ")");
	 

fun free id1 (ID id2) = if (id1 = id2) then  true else false|
    free id1 (APP(e1,e2))= (free id1 e1) orelse (free id1 e2) | 
    free id1 (LAM(id2, e1)) = if (id1 = id2) then false else (free id1 e1);
    
(* finds new variables which are fresh  in l and different from id*)
(* This is an improved version over the one provided*) 
fun findme id l = 
	if not (List.exists (fn x => id = x) l) then
		id
	else
		(findme (id^"'") l);
		

(* finds the list of free variables in a term *)
fun freeVars (ID id2)       = [id2]
  | freeVars (APP(e1,e2))   = freeVars e1 @ freeVars e2
  | freeVars (LAM(id2, e1)) = List.filter (fn x => not (x = id2)) (freeVars e1);
  
  
  
(*does substitution avoiding the capture of free variables*)
(* Substitute e for id in id1/(e1, e2)... *)

fun subs e id (ID id1) =  if id = id1 then e else (ID id1) |
    subs e id (APP(e1,e2)) = APP(subs e id e1, subs e id e2)|
    subs e id (LAM(id1,e1)) = (if id = id1 then LAM(id1,e1) else
                                   if (not (free id e1) orelse not (free id1 e)) then
										LAM(id1,subs e id e1)
                                   else 
										(let
											val id2 = (findme id ([id1]@ (freeVars e) @ (freeVars e1)))
										 in
											LAM(id2, subs e id (subs (ID id2) id1 e1)) 
										end));

	 
fun appToList expression [] = []
  | appToList expression (hd::tl) = (APP (expression, hd))::(appToList expression tl);

fun appFromList [] expression = []
  | appFromList (hd::tl) expression = (APP (hd, expression))::(appFromList tl expression);

fun lamToList expression [] = []
  | lamToList expression (hd::tl) = (LAM (expression, hd))::lamToList expression tl;

  
fun isBetaRedex (APP(LAM(_,_),_)) = true
  | isBetaRedex _ = false;

fun hasBetaRedex (LAM(x, y)) = hasBetaRedex y
  | hasBetaRedex (APP(a, b)) = (isBetaRedex (APP(a, b))) orelse hasBetaRedex a orelse hasBetaRedex b (* remember oresle short circuits *)
  | hasBetaRedex _ = false;
  
  (*beta-reduces a redex*)
fun betaRed (APP(LAM(id,e1),e2)) = subs e2 id e1;
  

(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)
  
fun leftmost (ID v) = [ID v]
  | leftmost (LAM (v, a)) =
	 if hasBetaRedex a then
		(LAM (v, a))::(tl (lamToList v (leftmost a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | leftmost (APP (a, b)) =
	if isBetaRedex (APP (a, b)) then
		(APP (a, b))::(leftmost(betaRed (APP(a, b))))
	else if isBetaRedex a then
		(APP (a, b))::(leftmost(APP((betaRed a), b)))
	else if (hasBetaRedex a) then (* no need to check a is not a redex due to order of statements *)
		let
			val abreduction = (appFromList (leftmost a) b)
		in
			abreduction@(tl (leftmost (List.last abreduction))) (* tl applied to remove duplicate of the beta normal of a applied to b *)
		end
	else if isBetaRedex b then
		(APP (a, b))::(leftmost(APP(a, (betaRed b))))
	else if (hasBetaRedex b) then (* changing b cannot create a redex, else AB would be a redex *)
		appToList a (leftmost b) (* Thus no recursive call on AB neccessary *)
	else (*No redexes *)
		[APP (a, b)];

(* Rightmost reduction, as above but with the application redexes resolved in a different order *)
fun rightmost (ID v) = [ID v]
  | rightmost (LAM (v, a)) =
	 if hasBetaRedex a then
		(LAM (v, a))::(tl (lamToList v (rightmost a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | rightmost (APP (a, b)) =
  	if ((not (isBetaRedex b)) andalso (hasBetaRedex b)) then 
		let
			val abreduction = (appToList  a (rightmost b))
		in
			abreduction@(tl (rightmost (List.last abreduction))) (* tl applied to remove duplicate of a applied to the beta normal form of b *)
		end
	else if isBetaRedex b then
		(APP (a, b))::(rightmost(APP(a, (betaRed b))))
	else if isBetaRedex (APP (a, b)) then
		(APP (a, b))::(rightmost(betaRed (APP(a, b))))
	else if ((not (isBetaRedex a)) andalso (hasBetaRedex a)) then
		let
			val abreduction = (appFromList (rightmost a) b)
		in
			abreduction@(tl (rightmost (List.last abreduction))) (* tl applied to remove duplicate of the beta normal of a applied to b *)
		end
	else if isBetaRedex a then
		(APP (a, b))::(rightmost(APP((betaRed a), b)))
	else (*No redexes *)
		[APP (a, b)];


fun betaReduce x = leftmost x;

fun isEtaRedex (LAM (v, (APP (a, ID b)))) = (v = b) andalso (not (free b a))
  | isEtaRedex _ = false;

fun hasEtaRedex (ID v) = false
  | hasEtaRedex (LAM (v, a)) = (isEtaRedex (LAM (v, a))) orelse (hasEtaRedex a)
  | hasEtaRedex (APP (a, b)) = (hasEtaRedex a) orelse (hasEtaRedex b);

fun etaRed (LAM (v, (APP (a, ID b)))) = a;

fun etaReduce (ID v) = [ID v]
  | etaReduce (LAM (v, a)) =
	 if isEtaRedex (LAM (v, a)) then
		(LAM (v, a))::(etaReduce (etaRed(LAM (v, a))))
	 else if hasEtaRedex a then
		(LAM (v, a))::(tl (lamToList v (etaReduce a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | etaReduce (APP (a, b)) =
	if isEtaRedex a then
		(APP (a, b))::(etaReduce(APP((etaRed a), b)))
	else if (hasEtaRedex a) then (* no need to check a is not a redex due to order of statements *)
		let
			val abreduction = (appFromList (etaReduce a) b)
		in		(* Recusrions required to ensure b is reduced *)
			abreduction@(tl (etaReduce (List.last abreduction))) (* tl applied to remove duplicate of the eta normal of a applied to b *)
		end
	else if isEtaRedex b then
		(APP (a, b))::(etaReduce(APP(a, (etaRed b))))
	else if (hasEtaRedex b) then (* There can be no eta redexes in A at this point, and application cannot be eta reduced *)
		appToList a (etaReduce b) (* Thus no recursive call on AB neccessary, only on b *)
	else (*No redexes *)
		[APP (a, b)];

		
fun printBetaReduction [] = print "\n"
  | printBetaReduction (hd::[]) = (printEXP hd; print "\n")
  | printBetaReduction (hd::tl) = (printEXP hd; print " -->\206\178\n"; printBetaReduction tl);
  
fun printEtaReduction [] = print "\n"
  | printEtaReduction (hd::[]) = (printEXP hd; print "\n")
  | printEtaReduction (hd::tl) = (printEXP hd; print " -->\206\183\n"; printEtaReduction tl);
  
fun printBetaEtaReduction [] = print "\n"
  | printBetaEtaReduction (hd::[]) = (printEXP hd; print "\n")
  | printBetaEtaReduction (hd::tl) = (printEXP hd; print " -->\206\178\206\183\n"; printBetaEtaReduction tl);

(* Translation function V *)
fun toItem (ID x) = IID x
  | toItem (LAM (x, y)) = ILAM (x, toItem y)
  | toItem (APP (a, b)) = IAPP (toItem b, toItem a);

(* Note that the ordering here is due to the inability to equality test during patern matching, 
*  f (x, x) is erronous in SML. Also due to the fact that any if statement must have an else clause. 
*  Also becuase ( CID x, CID y) and (CID x, COM y) are not mutually exclusive *)
fun f (CID x, CAPP (a, b)) = 
	if (((CID x) = b) andalso (not (Combinators.free (CID x) a))) then
		a
	else
		CAPP( CAPP (CS, f ((CID x), a)), f ((CID x), b))
  | f (CID x, a) =
	if ((CID x) = a) then (* Clause 1 *)
		CI 
	else (* clause 2 *)
		 CAPP (CK, a);

fun toCombinators (ID x) = CID x
  | toCombinators (APP (a, b)) = CAPP (toCombinators a, toCombinators b)
  | toCombinators (LAM (x, a)) = f (CID x, (toCombinators a));

val vx = (ID "x");
val vy = (ID "y");
val vz = (ID "z");
val t1 = (LAM("x",vx));
val t2 = (LAM("y",vx));
val t3 = (APP(APP(t1,t2),vz));
val t4 = (APP(t1,vz));
val t5 = (APP(t3,t3));
val t6 = (LAM("x",(LAM("y",(LAM("z",(APP(APP(vx,vz),(APP(vy,vz))))))))));
val t7 = (APP(APP(t6,t1),t1));
val t8 = (LAM("z", (APP(vz,(APP(t1,vz))))));
val t9 = (APP(t8,t3));
val omega = APP (LAM ("x", APP (ID "x", ID "x")), LAM ("x", APP (ID "x", ID "x")));

end


(*############ Item Functions ############*)
structure Item = struct

(* Note that the ordering here is due to the inability to equality test during patern matching, 
*  f (x, x) is erronous in SML. Also due to the fact that any if statement must have an else clause. 
*  Also becuase ( CID x, CID y) and (CID x, COM y) are not mutually exclusive *)
fun f (CID x, CAPP (a, b)) = 
	if (((CID x) = b) andalso (not (Combinators.free (CID x) a))) then
		a
	else
		CAPP( CAPP (CS, f ((CID x), a)), f ((CID x), b))
  | f (CID x, a) =
	if ((CID x) = a) then (* Clause 1 *)
		CI 
	else (* clause 2 *)
		 CAPP (CK, a);

fun toCombinators (IID x) = CID x
  | toCombinators (IAPP (a, b)) = CAPP (toCombinators b, toCombinators a)
  | toCombinators (ILAM (x, a)) = f (CID x, (toCombinators a));

fun printEXP (IID x) = print x
  | printEXP (ILAM (x, y)) = (
	print "[";
	print x;
	print "]";
	printEXP y
	)
  | printEXP (IAPP (a, b)) = (
	print "<";
	printEXP a;
	print ">";
	printEXP b
	);

val vx = IID "x";
val vy = IID "y";
val vz = IID "z";

val t1 = ILAM ("x", vx);
val t2 = ILAM ("y", vx);
val t3 = IAPP (vz, IAPP (t2, t1));
val t4 = IAPP (vz, t1);
val t5 = IAPP (t3, t3);
val t6 = ILAM("x", (ILAM ("y", (ILAM ("z", IAPP( IAPP (vz, vy), IAPP (vz, vx)))))));
val t7 = IAPP( t1, IAPP (t1, t6));
val t8 = ILAM("z", IAPP( IAPP (vz, t1), vz));
val t9 = IAPP (t3, t8);
val omega = IAPP (ILAM ("x", IAPP (IID "x", IID "x")), ILAM ("x", IAPP (IID "x", IID "x")));

end


(*############ DeBruijn Functions ############*)
structure Bruijn = struct

fun printEXP (BID x) = print (Int.toString x)
  | printEXP (BLAM x) = (
	print "(\206\187";
	printEXP x;
	print ")"
	)
  | printEXP (BAPP (a, b)) = (
	print "(";
	printEXP a;
	printEXP b;
	print ")"
	);

val vx = BID 1;
val vy = BID 2;
val vz = BID 3;

val t1 = BLAM (BID 1);
val t2 = BLAM (BID 2);
val t3 = BAPP (BAPP (t1, t2), BID 3);
val t4 = BAPP (BLAM (BID 1), BID 3);
val t5 = BAPP (BAPP (BAPP ( BLAM (BID 1), BLAM (BID 2)),BID 3), (BAPP (BAPP ( BLAM (BID 1), BLAM (BID 2)),BID 3)));
val t6 = BLAM (BLAM (BLAM ( BAPP (BAPP (BID 3, BID 2), BAPP (BID 2, BID 1)))));
val t7 = BAPP (BAPP ( t6, t1), t1);
val t8 = BLAM (BAPP (BID 1,BAPP( BLAM ( BID 1), BID 1)));
val t9 = BAPP (t8, t3);
val omega = BAPP ( BLAM (BAPP(BID 1, BID 1)), BLAM (BAPP(BID 1, BID 1)));
 

end


(*############ Item with DeBruijn Functions ############*)
structure ItemBruijn = struct

fun printEXP (IBID x) = print (Int.toString x)
  | printEXP (IBLAM x) = (
	print "[]";
	printEXP x
	)
  | printEXP (IBAPP (a, b)) = (
	print "<";
	printEXP a;
	print ">";
	printEXP b
	);

val vx = IBID 1;
val vy = IBID 2;
val vz = IBID 3;

val t1 = IBLAM (IBID 1);
val t2 = IBLAM (IBID 2);
val t3 = IBAPP (IBID 3, IBAPP (t2, t1));
val t4 = IBAPP (IBID 3, IBLAM (IBID 1));
val t5 = IBAPP ((IBAPP (IBID 3,IBAPP (IBLAM (IBID 2), IBLAM (IBID 1)))),IBAPP (IBID 3, IBAPP (IBLAM (IBID 2), IBLAM (IBID 1))));
val t6 = IBLAM (IBLAM (IBLAM ( IBAPP (IBAPP (IBID 1, IBID 2), IBAPP (IBID 2, IBID 3)))));
val t7 = IBAPP (t1, IBAPP ( t1, t6));
val t8 = IBLAM (IBAPP (IBAPP(IBID 1, IBLAM ( IBID 1)), IBID 1));
val t9 = IBAPP (t3, t8);
val omega = IBAPP ( IBLAM (IBAPP(IBID 1, IBID 1)), IBLAM (IBAPP(IBID 1, IBID 1)));
 
end
