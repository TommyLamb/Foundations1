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
	 
	 
(* This leftmost reduces the given term, returning a LEXP List listing each step in the order they are carried out *)

fun leftmost (ID v) = [ID v]
  | leftmost (LAM (v, a)) =
	 if has_redex a then
		(LAM (v, a))::addlam v (leftmost a)
	else
		[LAM (v, a)]
  | leftmost (APP (a, b)) =
	if is_redex (APP (a, b)) then
		(APP (a, b))::(leftmost(red (APP(a, b))))
	else if has_redex a then
		(APP (a, b))::(leftmost(APP((red a), b)))
	else if has_redex b then
		(APP (a, b))::(leftmost(APP(a, (red b))))
	else
		[APP (a, b)];