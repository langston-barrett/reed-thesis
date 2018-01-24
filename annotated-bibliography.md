## Annotated Bibliography

This is a list of texts I ended up reading to learn about HoTT and related subjects, with summaries of what they provide.

### The Curry-Howard Isomorphism

 * ["Propositions as Types"](http://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-types/propositions-as-types.pdf) - Wadler (12 pages): The best introduction to the Curry-Howard correspondence.

 * [On the Interpretation of Intuitionistic Logic](http://homepages.inf.ed.ac.uk/jmckinna/kolmogorov-1932.pdf) - Kolmogorov (1932, 7 pages): The Brouwer-Heyting-Kolmogorov interpretation is the basis for the Curry-Howard isomorphism. It states that we can reinterpret intuitionistic logic as related to "problems" and proofs as their "solutions" (programs).
 
 * [A Brief Introduction to the Intuitionistic Propositional Calculus](https://www.classes.cs.uchicago.edu/archive/2003/spring/15300-1/intuitionism.pdf) - Stuart A. Kurtz (8 pages): A concise introduction to the Curry-Howard isomorphism from the point of view of IPL.

### Type Theory

 * The works of Per Martin-Lof:

    - ["An Intuitionistic Theory of Types"](https://github.com/michaelt/martin-lof/blob/master/pdfs/An-Intuitionistic-Theory-of-Types-1972.pdf?raw=true) (1972, 45 pages): His first paper describing what we now call dependent type theory.

    - ["Constructive Mathematics and Computer Programming"](https://github.com/michaelt/martin-lof/blob/master/pdfs/Constructive-mathematics-and-computer-programming-1982.pdf?raw=true) (1982, 18 pages): His attempt to dumb things down for us computer scientists :) Real meat starts on page 4 of the PDF (page 170 of the text). Mostly a less formal summary of the 1972 paper.
      
    - [_Intuitionistic Type Theory_](http://www.csie.ntu.edu.tw/~b94087/ITT.pdf) (1980, 55 pages): This is a complete introduction to the theory. Surprisingly readable! Uses old terminology (calls types "sets" to make it more palatable for mathematicians).

### Homotopy Type Theory

 * Surveys:
 
    - ["Type Theory and Homotopy"](http://www.andrew.cmu.edu/user/awodey/preprints/TTH.pdf) - Awodey (20 pages): A survey article on all of the above. Gets into model categories, etc. Not very accessible.

    - ["Homotopy Type Theory and Voevodsky's Univalent Foundations"](https://arxiv.org/pdf/1210.5658.pdf) - Warren : Another survey. Long Coq tutorial at the end.

 * [_The HoTT Book_](https://homotopytypetheory.org/book/) aka The Book: This is the main text from which I've studied. Provides a comprehensive overview of the type theory before beginning on the homotopy, and really the 2nd chapter doesn't rely on much/any algebraic topology. 
 
### Algebraic Topology

Naturally, I didn't read the entirety of each of these, I mostly picked and chose what was helpful at the moment. 

 * _Topological Manifolds_ - Lee

 * _Algebraic Topology_ - Hatcher
 
 * _Topology and Groupoids_ - Ronald Brown: An elementary introduction to the fundamental groupoid. Requires no previous knowledge of the fundamental group or category theory. Non-standard notation/terminology (interval groupoid, path category).

 * _Categories for the Working Mathematician_ - Mac Lane: I don't forsee reading too much of this, but would enjoy it :)

 * _Category Theory_ - Awodey: I'm mostly reading this on the side.
 
### Blog Posts

 * ["Just Kidding: Understanding Identity Elimination in Homotopy Type Theory"](https://homotopytypetheory.org/2011/04/10/just-kidding-understanding-identity-elimination-in-homotopy-type-theory/) - Dan Licata: A great summary of the _J_ rule, or as the HoTT book calls it, "path induction". Explains why we can always assume equalities with no/one fixed endpoint(s) are `refl`.
 
### Articles

Many of these didn't directly contribute to my understanding of HoTT so much as provide ideas for topics, and re-contextualize ideas that you see in The Book.

 * ["Pattern Matching Without K"](https://lirias.kuleuven.be/bitstream/123456789/452283/2/icfp14-cockxA.pdf): Dependent pattern matching requires axiom K, which is incompatible with univalence. Can we come up with a restricted version which doesn't use/require K?

 * ["A Cubical Approach to Synthetic Homotopy Theory"](http://dlicata.web.wesleyan.edu/pubs/lb15cubicalsynth/lb15cubicalsynth.pdf) - Daniel Licata: Using "cubical" ideas to simplify proofs. [HoTT issue #689](https://github.com/HoTT/HoTT/issues/689) is a feature request from Mike Shulman to add this. Might be a good topic!

 * ["A Unification Algorithm for **Coq** Featuring Universe Polymorphism and Overloading"](https://people.mpi-sws.org/~beta/papers/unicoq.pdf) - Matthieu Sozeau: Readable even if you haven't heard of unification before. Good intuition behind how Coq fills in those `_`s.
 
 * ["Homotopy Type Theory: A synthetic approach to higher equalities"](https://arxiv.org/pdf/1601.05035.pdf) - Michael Shulman: This one is a great complement to the HoTT book, it discusses the philosophical implications for the use of HoTT as a foundations, with a lengthy and accessible discussion of so-called "identifications".
 
 * ["A Proposition is the (Homotopy) Type of its Proofs"](https://www.andrew.cmu.edu/user/awodey/preprints/tait.pdf) - Steve Awodey: Short, non-mathematical introduction to HoTT. Talks about a "two dimensional universe" of mathematics, where one dimension is universe level ("size") and the other is h-level ("complexity"). Talks about the interval groupoid. Discusses "impredicative encoding" of HITs.
 
 * ["100 years of Zermelo’s axiom of choice: what was the problem with it?"](https://link.springer.com/content/pdf/10.1007%2F978-1-4020-8926-8_10.pdf) - Martin-Lof: Talks about the axiom of choice in type theory. Great Bishop quote.
 
 * [F-algebras](https://en.wikipedia.org/wiki/F-algebra#External_links):
    - ["Categorical Programming with Inductive and Coinductive Types"](http://kodu.ut.ee/~varmo/papers/thesis.pdf): A thesis on initial algebras and final coalgebras for functors.
    - ["Recursive Types for Free!"](http://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt) - Wadler: An accessible introduction to initial algebras and final coalgebras for functors.
 
 * ["An  introduction  to  univalent  foundations  for mathematicians"](https://faculty.math.illinois.edu/~dan/Papers/ium.pdf) - Grayson

### W-types

 * ["Non-wellfounded Trees in Homotopy Type Theory"](https://arxiv.org/abs/1504.02949): The main inspiration for this thesis.

 * ["Representing inductively defined sets by wellorderings in Martin-Lof's type theory"](https://www.sciencedirect.com/science/article/pii/S0304397596001454) - Dybjer: "We prove that every strictly positive endofunctor on the category of [extensional types] has an initial algebra", and that these are W-types. Gives a breakdown of how to turn strictly positive functors into the form `Σ (a : A) (B a → X)`, and a few remarks on the intentional side.

 * ["Inductive Types in Homotopy Type Theory"](https://arxiv.org/abs/1201.3898) - Awodey, Gambino, Sojakova: A great review of the status of W-types in extensional theories. Proves certain rules about W-types with propositional computation rules equivalent to the existence of an initial algebra for a polynomial functor. 

 * ["Containers: Constructing strictly positive types"](http://www.sciencedirect.com/science/article/pii/S0304397505003373) - Abbott, Altenkirch, Ghani: Takes W-type thinking into the categorical setting, derives M-types from W-types.

 * [_Intuitionistic Type Theory_](http://www.csie.ntu.edu.tw/~b94087/ITT.pdf) (1980, 55 pages): One of the later sections is on W-types. Not nearly as accessible as the other papers mentioned here.

### Other links

 * [Learn Type Theory](https://github.com/jozefg/learn-tt): A resource guide. This list overlaps a lot with that one.

 * [Open problems in HoTT](https://ncatlab.org/homotopytypetheory/show/open+problems): On the HoTT wiki, which might prove useful.
   
    - "Show that the Klein bottle is not orientable. (This requires defining 'orientable'.)"
    - "Calculate more homotopy groups of spheres."
    - "Can we verify computational algebraic topology using HoTT?"
    
 * [Wiki: References](https://ncatlab.org/homotopytypetheory/show/References): I should read through this list to see if there's anything that we should read.
    
