datatype LEXP = APP of LEXP * LEXP
       | LAM of string * LEXP
       | ID of string;

fun printLEXP (ID v) = print v
  | printLEXP (LAM (v,e)) =
		(print "(\206\187";
		print v;
		print ".";
		printLEXP e;
		print ")")
  | printLEXP (APP(e1,e2)) =
    (print "(";
     printLEXP e1;
     print " ";
     printLEXP e2;
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

	 
fun isRedex (APP(LAM(_,_),_)) = true
  | isRedex _ = false;

fun hasRedex (LAM(x, y)) = hasRedex y
  | hasRedex (APP(a, b)) = (isRedex (APP(a, b))) orelse hasRedex a orelse hasRedex b (* remember oresle short circuits *)
  | hasRedex _ = false;


	 
(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)

fun appToList expression [] = []
  | appToList expression (hd::tl) = (APP (expression, hd))::(appToList expression tl);

fun appFromList [] expression = []
  | appFromList (hd::tl) expression = (APP (hd, expression))::(appFromList tl expression);

fun lamToList expression [] = []
  | lamToList expression (hd::tl) = (LAM (expression, hd))::lamToList expression tl;

  (*beta-reduces a redex*)
fun red (APP(LAM(id,e1),e2)) = subs e2 id e1;
  
fun leftmost (ID v) = [ID v]
  | leftmost (LAM (v, a)) =
	 if hasRedex a then
		(LAM (v, a))::(tl (lamToList v (leftmost a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | leftmost (APP (a, b)) =
	if isRedex (APP (a, b)) then
		(APP (a, b))::(leftmost(red (APP(a, b))))
	else if isRedex a then
		(APP (a, b))::(leftmost(APP((red a), b)))
	else if isRedex b then
		(APP (a, b))::(leftmost(APP(a, (red b))))
	else if (hasRedex a) then (* no need to check a is not a redex due to order of statements *)
		let
			val abreduction = (appFromList (leftmost a) b)
		in
			abreduction@(tl (leftmost (List.last abreduction))) (* tl applied to remove duplicate of the beta normal of a applied to b *)
		end
	else if (hasRedex b) then (* changing b cannot create a redex, else AB would be a redex *)
		appToList a (leftmost b) (* Thus no recursive call on AB neccessary *)
	else (*No redexes *)
		[APP (a, b)];

(* Rightmost reduction, as above but with the application redexes resolved in a different order *)
fun rightmost (ID v) = [ID v]
  | rightmost (LAM (v, a)) =
	 if hasRedex a then
		(LAM (v, a))::(tl (lamToList v (rightmost a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | rightmost (APP (a, b)) =
  	if ((not (isRedex b)) andalso (hasRedex b)) then 
		let
			val abreduction = (appToList  a (rightmost b))
		in
			abreduction@(tl (rightmost (List.last abreduction))) (* tl applied to remove duplicate of a applied to the beta normal form of b *)
		end
	else if isRedex b then
		(APP (a, b))::(rightmost(APP(a, (red b))))
	else if ((not (isRedex a)) andalso (hasRedex a)) then
		let
			val abreduction = (appFromList (rightmost a) b)
		in
			abreduction@(tl (rightmost (List.last abreduction))) (* tl applied to remove duplicate of the beta normal of a applied to b *)
		end
	else if isRedex a then
		(APP (a, b))::(rightmost(APP((red a), b)))
	else if isRedex (APP (a, b)) then
		(APP (a, b))::(rightmost(red (APP(a, b))))
	else (*No redexes *)
		[APP (a, b)];

		
		
fun printBetaReduction [] = print "\n"
  | printBetaReduction (hd::[]) = (printLEXP hd; print "\n")
  | printBetaReduction (hd::tl) = (printLEXP hd; print " -->\206\178\n"; printBetaReduction tl);
  
fun printEtaReduction [] = print "\n"
  | printEtaReduction (hd::[]) = (printLEXP hd; print "\n")
  | printEtaReduction (hd::tl) = (printLEXP hd; print " -->\206\183\n"; printEtaReduction tl);
  
fun printReduction [] = print "\n"
  | printReduction (hd::[]) = (printLEXP hd; print "\n")
  | printReduction (hd::tl) = (printLEXP hd; print " -->\206\178\206\183\n"; printReduction tl);

fun reduce x = printReduction(leftmost x);
fun reduction x = List.last(leftmost x);
