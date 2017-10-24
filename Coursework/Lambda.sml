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

	 
(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)

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
	if (((CID x) = b) andalso (not (Combinatorics.free (CID x) a))) then
		a
	else
		CAPP( CAPP (CS, f ((CID x), a)), f ((CID x), b))
  | f (CID x, a) =
	if ((CID x) = a) then (* Clause 1 *)
		CI 
	else (* clause 2 *)
		 CAPP (CK, a); (* See comment on supporting documentation for omission of conditional *)

fun toCombinatorics (ID x) = CID x
  | toCombinatorics (APP (a, b)) = CAPP (toCombinatorics a, toCombinatorics b)
  | toCombinatorics (LAM (x, a)) = f (CID x, (toCombinatorics a));

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
