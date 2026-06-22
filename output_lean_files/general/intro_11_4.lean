/-
TASK ID: intro_11_4
TYPE: Remark
SOURCE PLAN: chapter11-data-compression

This parent-facing file is a non-proof textual carrier for source narrative.
It preserves the remark text for Phase 2 status accounting and exports no
mathematical dependency.
-/

/-- Textual carrier for `Application: Data Compression`. -/
def intro_11_4 : String :=
  "\\subsection*{11.4 Application: Data Compression}\n\nLet A ={ a1,a 2,...,a m}" ++
  " denote an alphabet of size m. Suppose we generate\n\na string of length n, " ++
  "with each character drawn independently according to a\n\nprobability " ++
  "distribution P(ai) = pi , where pi 's are nonnegative real numbers\n\n" ++
  "summing to 1. There are totally mn combinations. We may associate each " ++
  "string\n\nwith an integer between 1 and mnU s i n g log2(mn) bits, we can " ++
  "store and recover\n\nthe random string with no decoding error.\n\nHowever, if " ++
  "we allow an arbitrarily small error in decoding, we can significantly\n\n" ++
  "reduce the number of bits. It turns out there exists a set S\\subset A n " ++
  "with probability\n\nPr(S)\\geq 1 - \\epsilon and \\vertS\\vert\\ll mn. We only " ++
  "encode the strings in the set S The strings\n\nnot in S are not encoded, or " ++
  "encoded arbitrarily. The decoding error is thus less than\n\nor equal to " ++
  "\\epsilon. We will show that \\epsiloncan be made arbitrarily small as the " ++
  "block length\n\nn increases, with the cardinality of the set S roughly equal" ++
  " to .2nH(P) , where H(P)\n\ndenotes the entropy of the distribution P ,\n\n" ++
  "H(P) \\coloneqq-\n\nm\\sum\n\ni=1\n\npi log2 pi.\n\nTo realize this idea, we fix a " ++
  "parameter \\delta> 0 and define a set S\\delta,n of strings by\n\n" ++
  "S\\delta,n\\coloneqq{ (x1,x 2,...,x n)\\inA n :2 -n(H(P) +\\delta) \\leq\n\nn\n\n" ++
  "k=1\n\np(xk)\\leq 2 -n(H(P) -\\delta)}.\n\nWe claim that for any fixed \\delta> " ++
  "0,t h e s e t S\\delta,n has probability arbitrarily close to 1\n\n" ++
  "asn\\to\\infty We denote the random string of length n by. X, and for k= 1 " ++
  ",2,...,n ,\n\nlet Xk be the k -th letter in X. Define a new random variable " ++
  "Uk =- log2 P(Xk),\n\nwhere P(Xk) is equal to pi if Xk =i For simplicity, we " ++
  "may assume pi >0 for\n\nall i , so that log2 pi is well-defined. The " ++
  "expectation of Uk is precisely equal to the\n\nentropy H(P) of distribution " ++
  "P By the weak law of large numbers, for any fixed\n\n\\delta> 0,we have\n\n" ++
  "limn\\to\\infty Pr\n\n( \\vert\\vert\\vert 1\n\nn\n\nn\\sum\n\nk=1\n\nUk -H(P)\n\n" ++
  "\\vert\\vert\\vert \\leq\\delta\n\n)\n\n=1 .\n\nBut\n\n\\vert\\vert\\vert 1\n\nn\n\nn\\sum\n\nk=1" ++
  "\n\nUk -H(P)\n\n\\vert\\vert\\vert \\leq\\delta 2 n(H(P) -\\delta) \\leq2 " ++
  "U1+U2+\\cdot\\cdot\\cdot+Un \\leq2 n(H(P) +\\delta)\n\n2 -n(H(P) +\\delta) \\leqP(X" ++
  " 1)P(X 2)\\cdot\\cdot\\cdot P(Xn)\\leq 2 -n(H(P) -\\delta).\n\nThe random string " ++
  "X belongs toS\\delta,n if and only if .\n\n\\vert\\vert\\vert 1\n\nn\n\n\\sumn\n\nk=1 " ++
  "Uk -H(P)\n\n\\vert\\vert\\vert \\leq\\deltaT h i s\n\nshows that the probability of" ++
  " the set of strings S\\delta,n approaches 1 asn\\to\\infty , for any\n\nfixed " ++
  "\\delta> 0. To estimate the cardinality of S\\delta,n, we note that all " ++
  "random strings in\n\nS\\delta,n have probability at least .2-n(H(P) " ++
  "+\\delta)There are at most .2n(H(P) +\\delta) strings in\n\nS\\delta,n. We can " ++
  "represent them using at most n(H(P) + \\delta) bits.\n\nTo design the data " ++
  "compression scheme with decoded error no more than \\epsilon,w e\n\nfirst fix" ++
  " a small \\delta> 0 and find a sufficiently large block length n such that " ++
  "Pr(X\\in\n\nS\\delta,n)> 1 - \\epsilon. Because we only encode the strings in " ++
  "S\\delta,n,it takes H(P) + \\deltabits\n\nper symbol. The saving is " ++
  "particularly significant if H(P) \\ll log2(m).\n\nThe result demonstrated in " ++
  "this example is the forward part of Shannon's theorem\n\non data " ++
  "compression. This is one of the first major results in information theory " ++
  "[ 3].\n\nWe demonstrate the idea of this data compression with finite block " ++
  "length n.\n\nSuppose that alphabet is A ={ a,b,c }The data source generates " ++
  "symbols a, b,\n\nand c independently, according to the distribution P(a) = " ++
  "2/3, P(b) = 2/9 and\n\nP(c) = 1/9. We group the random symbols into groups " ++
  "of size n = 11 and use\n\nB bits to encode each group. Only the .2B - 1 " ++
  "strings of length n with the largest\n\nprobabilities are encoded. If the " ++
  "random string is not among these .2B - 1 selected\n\nones, we use a special " ++
  "number, such as . 2B , to signify that a decoding error has\n\noccurred.\n\n" ++
  "The probability of error is calculated by the following Python program.\n\n" ++
  "Python Program for Demonstrating Data Compression\n\n# Compute the success " ++
  "decoding probability of\n\n# data compression with fixed block length\n\nfrom " ++
  "numpy import prod\n\nfrom itertools import product\n\nn = 11 # block length\n\n" ++
  "prob_dist= {'a':2/3, 'b':2/9, 'c':1/9}\n\nB=1 6\n\nA = [x for x in prob_dist] " ++
  "# list of letters\n\nD={}\n\nfor t in product(A,repeat = n):\n\ns = ''join(t)\n\n" ++
  "D[s] = prod([prob_dist[x] for x in t])\n\n# sum the largest 2 **B-1 " ++
  "probabilities\n\nlist_of_prob = list(Dvalues())\n\nlist_of_probsort(reverse = " ++
  "True)\n\nprob_success = sum(list_of_prob[0:(2 **B-1)])\n\nprint(f\"{B} bits per" ++
  " block\")\n\nprint(f\"P(successful decoding) = {prob_success}\")\n\nThe table " ++
  "below shows the probabilities of successful decoding for a different\n\n" ++
  "number of bits per block. The probabilities are obtained by running the " ++
  "Python\n\nprogram forB = 8, 9,..., 16.\n\nNo. of bits per block 8 9 10 11 12 " ++
  "13 14 15 16\n\nP (successful decoding) 0.245 0.327 0.428 0.533 0.650 0.765 " ++
  "0.864 0.939 0.983\n\nWe observe that the value of .11 \\cdot H(P) = 11(1.22) " ++
  "13.475, where H(P)\n\n1.22 is entropy of the probability distribution P The " ++
  "table shows that there is a\n\nsignificant increase in the probability of " ++
  "successful decoding when the number of\n\nbits per block is slightly above " ++
  "the threshold value, ie., for B= 14 or higher.\n\nIn general, as the block " ++
  "length n approaches infinity, there is an abrupt increase\n\nin success " ++
  "probability when the number of bits per block is .1.22n."
