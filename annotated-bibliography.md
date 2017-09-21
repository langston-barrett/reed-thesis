## Reading List

I would recommend that you read the first two papers (Wadler and Kolmogorov) before our next meeting, they should provide the necessary motivation. I think we should both read Awodey's survey and that of Pelayo and Warren. Personally, I'd also like to get through another 50 pages of _Type Theory and Functional Programming_.

In the next three weeks, I'd ideally finish most of _Type Theory and Functional Programming_ and move on to studying dependent type theory. I think in week 4, we could start looking at the Homotopy Type Theory master's thesis and see if it makes any sense yet.

## Annotated Bibliography

### The Curry-Howard Isomorphism

 * ["Propositions as Types"](http://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf) - Wadler (12 pages): The best introduction to the Curry-Howard correspondence.

 * [On the Interpretation of Intuitionistic Logic](http://homepages.inf.ed.ac.uk/jmckinna/kolmogorov-1932.pdf) - Kolmogorov (1932, 7 pages): The Brouwer-Heyting-Kolmogorov interpretation is the basis for the Curry-Howard isomorphism. It states that we can reinterpret intuitionistic logic as related to "problems" and proofs as their "solutions" (programs).

### Type Theory

 * _Type Theory and Functional Programming_ - Thompson: An introduction to basic logic and type theory aimed at undergraduates. I'm on page 50/400, and think I could be finished with the book in a month and a half or less.
   
 * _Types and Programming Languages_: A widely used book on types from a more practical, CS perspective. Recommended by Dylan. Has a companion _Advanced Topics in Types and Programming Languages_ which covers dependent types.
   
 * [_Proofs and Types_](http://www.paultaylor.eu/stable/prot.pdf) - Girard: A less approachable (graduate level) introduction to classical type theory.
   
 * _An Introduction to Mathematical Logic and Type Theory: To Truth Through Proof_: Another undergraduate type theory textbook.

 * The works of Per Martin-Lof:

    - ["An Intuitionistic Theory of Types"](https://github.com/michaelt/martin-lof/blob/master/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf?raw=true) (1972, 45 pages): His first paper describing what we now call dependent type theory.

    - ["Constructive Mathematics and Computer Programming"](https://github.com/michaelt/martin-lof/blob/master/pdfs/Constructive-mathematics-and-computer-programming-1982.pdf?raw=true) (1982, 18 pages): His attempt to dumb things down for us computer scientists :) Real meat starts on page 4 of the PDF (page 170 of the text). Mostly a less formal summary of the 1972 paper.
      
    - [_Intuitionistic Type Theory_](http://www.csie.ntu.edu.tw/~b94087/ITT.pdf) (1980, 55 pages): This is a complete introduction to the theory. Surprisingly readable! Uses old terminology (calls types "sets" to make it more palatable for mathematicians).

### Homotopy Type Theory

 * Surveys:
 
    - ["Type Theory and Homotopy"](http://www.andrew.cmu.edu/user/awodey/preprints/TTH.pdf) - Awodey (20 pages): A survey article on all of the above.

    - ["Homotopy Type Theory and Voevodsky's Univalent Foundations"](https://arxiv.org/pdf/1210.5658.pdf): Another survey.

 * [_A Master's Thesis on Homotopy Type Theory_](https://homotopytypetheory.org/2012/08/18/a-master-thesis-on-homotopy-type-theory/) - Rijke (2012, 97 pages): An extensive review of the applications of identity types, which form a core part of the (type) theory of HoTT.
   
 * [_The HoTT Book_](https://homotopytypetheory.org/book/)
 
### Algebraic Topology

 * _Topological Manifolds_ - Lee

 * _Algebraic Topology_ - Hatcher: Best figures I've ever seen

 * _Categories for the Working Mathematician_ - Mac Lane: I don't forsee reading too much of this, but would enjoy it :)

### Other links

 * [Learn Type Theory](https://github.com/jozefg/learn-tt): A resource guide. This list overlaps a lot with that one.

 * [Open problems in HoTT](https://ncatlab.org/homotopytypetheory/show/open+problems): On the HoTT wiki, which might prove useful.
   
    - "Show that the Klein bottle is not orientable. (This requires defining 'orientable'.)"
    - "Calculate more homotopy groups of spheres."
    - "Can we verify computational algebraic topology using HoTT?"
    
 * [Wiki: References](https://ncatlab.org/homotopytypetheory/show/References): I should read through this list to see if there's anything that we should read.
    
