(* open List;*)

(* finds new variables which are fresh  in l and different from id*)
(* This is an improved version over the one provided*) 
fun findme id l = 
	if not (List.exists (fn x => id = x) l) then
		id
	else
		(findme (id^"'") l);
		
		
(* Print a term, using the lambda character*)
					 
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
	 
fun is_redex (APP(LAM(_,_),_)) = true
  | is_redex _ = false;

fun has_redex (LAM(x, y)) = has_redex y
  | has_redex (APP(a, b)) = (is_redex (APP(a, b))) orelse has_redex a orelse has_redex b (* remember oresle short circuits *)
  | has_redex _ = false;


	 
(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)

fun appToList expression [] = []
  | appToList expression (hd::tl) = (APP (expression, hd))::(appToList expression tl);

fun appFromList [] expression = []
  | appFromList (hd::tl) expression = (APP (hd, expression))::(appFromList tl expression);

fun lamToList expression [] = []
  | lamToList expression (hd::tl) = (LAM (expression, hd))::lamToList expression tl;

fun leftmost (ID v) = [ID v]
  | leftmost (LAM (v, a)) =
	 if has_redex a then
		(LAM (v, a))::(tl (lamToList v (leftmost a))) (* tl prevents duplication of this state *)
	else
		[LAM (v, a)]
  | leftmost (APP (a, b)) =
	if is_redex (APP (a, b)) then
		(APP (a, b))::(leftmost(red (APP(a, b))))
	else if is_redex a then
		(APP (a, b))::(leftmost(APP((red a), b)))
	else if is_redex b then
		(APP (a, b))::(leftmost(APP(a, (red b))))
	else if (has_redex a) then
		let
			val abreduction = (appFromList (leftmost a) b)
		in
			abreduction@(tl (leftmost (List.last abreduction))) (* tl applied to remove duplicate of the beta normal of a applied to b *)
		end
	else if (has_redex b) then (* changing b cannot create a redex, else AB would be a redex *)
		appToList a (leftmost b) (* Thus no recursive call on AB neccessary *)
	else (*No redexes *)
		[APP (a, b)];


fun printReduction [] = print "\n"
  | printReduction (hd::[]) = (printLEXP hd; print "\n")
  | printReduction (hd::tl) = (printLEXP hd; print " -->\n"; printReduction tl);

fun reduce x = printReduction(leftmost x);
fun reduction x = List.last(leftmost x);
