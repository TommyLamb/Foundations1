datatype COM = CAPP of COM*COM
       | CID of string
       | CI
       | CK
       | CS;
	   
fun printCEXP (CID v) = print v
  | printCEXP (CI) = print "I"
  | printCEXP (CS) = print "S"
  | printCEXP (CK) = print "K"
  | printCEXP (CAPP (a, b)) = (
	print "("; 
	printCEXP a;
	print " ";
	printCEXP b;
	print ")"
	);

fun isCRedex (CAPP (CI, v)) = true
  | isCRedex (CAPP ((CAPP (CK, v1)), v2)) = true 
  | isCRedex (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = true
  | isCRedex _ = false;

fun hasCRedex (CAPP (x, y)) = (isCRedex (CAPP (x, y))) orelse hasCRedex x orelse hasCRedex y 
  | hasCRedex _ = false;

fun cappToList expression [] = []
  | cappToList expression (hd::tl) = (CAPP (expression, hd))::(cappToList expression tl);

fun cappFromList [] expression = []
  | cappFromList (hd::tl) expression = (CAPP (hd, expression))::(cappFromList tl expression);

fun cRed (CAPP (CI, v)) = v
  | cRed (CAPP ((CAPP (CK, v1)), v2)) = v1 
  | cRed (CAPP ((CAPP ((CAPP (CS, v1)), v2)), v3)) = CAPP ((CAPP ( v1, v3)), (CAPP ( v2, v3)));

  (* For comments see Lamda.leftmost *)
fun cReduce (CID v) = [CID v]
  | cReduce (CI) = [CI]
  | cReduce (CK) = [CK]
  | cReduce (CS) = [CS]
  | cReduce (CAPP (a, b)) = 
	if (isCRedex (CAPP(a, b))) then
		(CAPP(a, b))::(cReduce (cRed (CAPP(a, b))))
	else if (isCRedex a) then
		(CAPP(a, b))::(cReduce (CAPP ((cRed a), b)))
	else if (isCRedex b) then	
		(CAPP(a, b))::(cReduce (CAPP (a, (cRed b))))
	else if (hasCRedex a) then
		let 
			val abreduction = (cappFromList (cReduce a) b)
		in
			abreduction@(tl (cReduce (List.last abreduction)))
		end
	else if (hasCRedex b) then
		cappToList a (cReduce b)
	else
		[CAPP (a, b)];
  

		
fun cPrintReduction [] = print "\n"
  | cPrintReduction (hd::[]) = (printCEXP hd; print "\n")
  | cPrintReduction (hd::tl) = (printCEXP hd; print " -->\n"; cPrintReduction tl);
  

fun cPrintReductionCount x = (
		cPrintReduction x;
		print "Steps: ";
		print (Int.toString((List.length x)-1));
		print "\n"
		);
  
fun cSubtermsList (CID v) = [CID v]
  | cSubtermsList (CI) = [CI]
  | cSubtermsList (CK) = [CK]
  | cSubtermsList (CS) = [CS]
  | cSubtermsList (CAPP (a, b)) = [CAPP (a, b)]@(cSubtermsList a)@(cSubtermsList b);

  
fun setify [] = []
  | setify (hd::tl) = 
	if (List.exists (fn x => hd = x) tl) then
		setify tl
	else
		hd::setify tl;

fun cSubterms x = setify (cSubtermsList x);

val red3 =  (CAPP ((CAPP ((CAPP (CS, CID "v1")), CID "v2")), CID "v3"));
