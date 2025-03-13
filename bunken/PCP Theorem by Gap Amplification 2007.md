The PCP Theorem by Gap Ampliﬁcation
IRIT DINUR
The Hebrew University, Jerusalem, Israel
Abstract. The PCP theorem [Arora and Safra 1998; Arora et. al. 1998] says that every language in
NP has a witness format that can be checked probabilistically by reading only a constant number
of bits from the proof. The celebrated equivalence of this theorem and inapproximability of certain
optimization problems, due to Feige et al. [1996], has placed the PCP theorem at the heart of the area
of inapproximability.
In this work, we present a new proof of the PCP theorem that draws on this equivalence. We give a
combinatorial proof for the NP-hardness of approximating a certain constraint satisfaction problem,
which can then be reinterpreted to yield the PCP theorem.
Our approach is to consider the unsat value of a constraint system, which is the smallest fraction of
unsatisﬁed constraints, ranging over all possible assignments for the underlying variables. We describe
a new combinatorial ampliﬁcation transformation that doubles the unsat-value of a constraint-system,
with only a linear blowup in the size of the system. The ampliﬁcation step causes an increase in
alphabet-size that is corrected by a (standard) PCP composition step. Iterative application of these
two steps yields a proof for the PCP theorem.
The ampliﬁcation lemma relies on a new notion of “graph powering” that can be applied to systems
of binary constraints. This powering ampliﬁes the unsat-value of a constraint system provided that
the underlying graph structure is an expander.
We also extend our ampliﬁcation lemma towards construction of assignment testers (alter-
natively, PCPs of Proximity) which are slightly stronger objects than PCPs. We then construct
PCPs and locally-testable codes whose length is linear up to a polylog factor, and whose correct-
ness can be probabilistically veriﬁed by making a constant number of queries. Namely, we prove
SAT ∈PCP 1
2 ,1[log2(n · poly log n), O(1)].
Categories and Subject Descriptors: F.2 [Theory of Computation]: Analysis of Algorithms and
Problem Complexity
General Terms: Theory, Algorithms
Additional Key Words and Phrases: Gap ampliﬁcation, PCP
ACM Reference Format:
Dinur, I. 2007. The PCP theorem by gap ampliﬁcation. J. ACM 54, 3, Article 12 (June 2007),
44 pages. DOI = 10.1145/1236457.1236459 http://doi.acm.org/ 10.1145/1236457.1236459
This work was supported by the Israel Science Foundation.
Authors’ address: The Selim and Rachel Benin School of Computer Science and Engineering, The
Hebrew University of Jerusalem, Ross Building, Givat Ram Campus, 91904 Jerusalem, Israel.
Permission to make digital or hard copies of part or all of this work for personal or classroom use is
granted without fee provided that copies are not made or distributed for proﬁt or direct commercial
advantage and that copies show this notice on the ﬁrst page or initial screen of a display along with the
full citation. Copyrights for components of this work owned by others than ACM must be honored.
Abstracting with credit is permitted. To copy otherwise, to republish, to post on servers, to redistribute
to lists, or to use any component of this work in other works requires prior speciﬁc permission and/or
a fee. Permissions may be requested from Publications Dept., ACM, Inc., 2 Penn Plaza, Suite 701,
New York, NY 10121-0701 USA, fax +1 (212) 869-0481, or permissions@acm.org.
C⃝2007 ACM 0004-5411/2007/06-ART12 $5.00 DOI 10.1145/1236457.1236459 http://doi.acm.org/
10.1145/1236457.1236459
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
2
IRIT DINUR
1. Introduction
A language L is in the class NP if there is a deterministic polynomial-time algorithm
called a veriﬁer that, in addition to the input, has access to a ‘proof’ such that the
following holds: If x ∈L then there is a proof causing the veriﬁer to accept, and if
x ̸∈L the veriﬁer will reject regardless of the proof.
The PCP theorem is a strong characterization of the class NP. The notion of
Probabilistically Checkable Proofs (PCPs) extends the power of the veriﬁer by
allowing it some randomness (and oracle access to the proof), and simultaneously
restricts the veriﬁer to read only a small number of symbols from the proof. More
formally, the class PCP[r, q] is deﬁned to contain all languages L for which there
is a veriﬁer V that uses O(r) random bits, reads O(q) bits from the proof, and
guarantees the following:
—If x ∈L then there is a proof π such that Pr[V π(x) accepts] = 1. (Here and
elsewhere V π(x) denotes the output of V on input x and proof π.)
—If x ̸∈L then for any proof π, Pr[V π(x) accepts] ≤1
2.
The PCP theorem says that every language in NP has a veriﬁer that uses at most
O(log n) random bits and reads only O(1) bits from the proof. In other words,
THEOREM 1.1(PCP THEOREM, [ARORA AND SAFRA 1998; ARORA ET AL. 1998]).
NP ⊆PCP[log n, 1].
This theorem was a great surprise, as it completely revises our concept of a proof.
Rather than the classical notion of a proof as a sequential object that if erroneous
in even one place can easily prove a false statement. The PCP theorem provides a
new proof notion that is more robust, and must be erroneous in many places when
attempting to prove a falsity.
Historically, the class PCP[r, q] stemmed out of the celebrated notion of inter-
active proofs [Goldwasser et al. 1989; Babai 1985] and the class IP. The original
motivation for deﬁning IP was cryptographic, but it soon lead to a list of remarkable
complexity-theoretic results, including for example IP = PSPACE (see Lund et al.
[1992] and Shamir [1992]). We will not give a detailed historic account that can be
found in, say, Arora [1994]. Let us just mention that an exciting sequence of papers
(see Ben-Or et al. [1988], Fortnow et al. [1994], and Babai et al. [1991]) lead to the
following theorem: the class of all languages with exponential-sized proofs is equal
to the class of all languages that can be veriﬁed by a (randomized) polynomial-time
veriﬁer. At this point attempts were made to “scale down” this result so as to char-
acterize the class NP in similar terms, through suitable restriction of the veriﬁer.
This was especially motivated by the discovery of Feige et al. [1996] that connected
such a scale-down to an inapproximability result for the clique number (see below).
This scale-down was achieved partially in Arora and Safra [1998] and completed
in Arora et al. [1998] and came to be known as the PCP theorem.
The techniques that lead to the proof were mainly algebraic, including low-
degree extension over ﬁnite ﬁelds, low-degree test, parallelization through curves,
a sum-check protocol, and the Hadamard and quadratic functions encodings.
1.1. PCP AND INAPPROXIMABILITY.
As mentioned above, the discovery of the
PCP theorem came hand in hand with the beautiful and surprising connection,
discovered by Feige et al. [1996], between PCP characterizations of NP and the
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
3
hardness of approximating the clique number in a graph. Predating these devel-
opments the situation regarding approximation problems was unclear. There was
no clue why different approximation problems seem to exhibit different approx-
imation behavior. The PCP theorem implied, for the ﬁrst time, that numerous
problems (including, for example, max-3-SAT) are hard to approximate. This has
had a tremendous impact on the study of combinatorial optimization problems, and
today the PCP theorem stands at the heart of nearly all hardness-of-approximation
results.
The connection to inapproximability is best described through constraint satis-
faction problems. Let us begin by deﬁning a constraint,
Deﬁnition 1.2.
Let V = {v1, . . . , vn} be a set of variables, and let  be a
ﬁnite alphabet. A q-ary constraint (C, i1, . . . , iq) consists of a q-tuple of indices
i1, . . . , iq ∈[n] and a subset C ⊆q of “acceptable” values. A constraint is
satisﬁed by a given assignment a : V → iff (a(vi1), a(vi2), . . . , a(viq)) ∈C.
The constraint satisfaction problem (CSP) is the problem of, given a system of
constraints C = {c1, . . . , cn} over a set of variables V , deciding whether there
is an assignment for the variables that satisﬁes every constraint. This problem
is clearly NP-complete as it generalizes many well known NP-complete problems
suchas3-SATand3-colorability.Forexample,intheequivalentofthe3-colorability
problem, the alphabet is  = {1, 2, 3} and the binary constraints are of the form
(C, i1, i2) where C = {(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)} consists of 6 out of
the possible 9 values that exclude equality.
An optimization version of this problem, called max-CSP, is to ﬁnd an assignment
that satisﬁes a maximum number of constraints. Let C = {c1, . . . , cn} be a set of
constraints over a set of variables V , in this paper we consider the unsat-value of C,
denoted UNSAT(C), deﬁned to be the smallest fraction of unsatisﬁed constraints, over
all possible assignments for V . Clearly C is satisﬁable if and only if UNSAT(C) = 0.
In this notation, the following theorem is a typical inapproximability result.
THEOREM 1.3 (INAPPROXIMABILITY VERSION OF PCP THEOREM).
There are
integers q > 1 and || > 1 such that, given as input a collection C of q-ary
constraints over an alphabet , it is NP-hard to decide whether UNSAT(C) = 0 or
UNSAT(C) ≥1
2.
Such a theorem is proven by showing a polynomial-time reduction from an NP-
complete language L, reducing an instance x to a constraint system Cx, such that
the following gap property holds: if x ∈L, then UNSAT(Cx) = 0 and if x ̸∈L then
UNSAT(Cx) ≥1
2.
The point is that the above Theorem 1.3 is equivalent to the PCP theorem (The-
orem 1.1).
LEMMA 1.4.
Theorem 1.1 and Theorem 1.3 are equivalent.
PROOF.
Let us brieﬂy explain this equivalence.
(⇒) Theorem 1.1 states that every NP language (and let us ﬁx some language
L ∈N P) has a veriﬁcation procedure Ver that reads c log n random bits, accesses
q = O(1) bits from the proof and decides whether to accept or reject (where
q and c are constants). For each ﬁxed random bit pattern r ∈{0, 1}c log n, Ver
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
4
IRIT DINUR
(deterministically) reads a ﬁxed set of q bits from the proof: i(r)
1 , . . . , i(r)
q . Denote
by C(r) ⊆{0, 1}q the possible contents of the accessed proof bits that would cause
Ver to accept.
We present a reduction from L to gap constraint satisfaction. Let x
?∈L be the
input, and denote n = |x|. Let  = {0, 1} and put a Boolean variable for each proof
location accessed by Ver on input x (so there are at most q2c log n = qnc Boolean
variables). Next, construct a system of constraints Cx = {cr}r∈{0,1}c log n such that the
constraint cr is deﬁned by cr = (C(r), i(r)
1 , . . . , i(r)
q ). It remains to observe that the
rejection probability of Ver is exactly equal UNSAT(Cx) so it is zero if x ∈L, and at
least 1
2 if x ̸∈L.
(⇐) For the converse, assume there is a reduction taking instances of any NP-
language into constraint systems such that the gap property holds. Here is how to
construct a veriﬁer. The veriﬁer will ﬁrst (deterministically) compute the constraint
system output by the reduction guaranteed above. It will expect the proof to consist
of an assignment for the variables of the constraint system. Next, the veriﬁer will
use its random string to select a constraint uniformly at random, and check that the
assignment satisﬁes it, by querying the proof at the appropriate locations.
The (⇒) direction of the equivalence has so far been the more useful one, as it
enables us to derive inapproximability results from the PCP theorem. In this work,
we rely on the converse (⇐) direction, to give a new “inapproximability-based”
proof for the PCP theorem. We ﬁnd it especially pleasing that our proof has a similar
ﬂavor to the area in which the theorem has been most applicable.
1.2. CONSTRAINT GRAPHS AND OPERATIONS ON THEM.
Our approach for prov-
ing the PCP Theorem (as stated in Theorem 1.3) is based on an iterative gap am-
pliﬁcation step. For this, we restrict attention to systems of binary (two-variable)
constraints, such as 3-colorability constraints. Any binary constraint system nat-
urally deﬁnes an underlying graph, in which the variables are vertices, and two
variables are adjacent iff there is a constraint over them. We call this a constraint
graph.
Deﬁnition 1.5 (Constraint Graph).
G = ⟨(V, E), , C⟩is called a constraint
graph, if
(1) (V, E) is an undirected graph, called the underlying graph of G.
(2) The set V is also viewed as a set of variables assuming values over alphabet .
(3) Each edge e ∈E, carries a constraint c(e) ⊆ × , and C = {c(e)}e∈E . A
constraint c(e) is said to be satisﬁed by (a, b) iff (a, b) ∈c(e).
We sometimes use the same letter G to denote the constraint graph and the
underlying graph (V, E).
An assignment is a mapping σ : V → that gives each vertex in V a value
from . For any assignment σ, deﬁne
UNSATσ(G) =
Pr
(u,v)∈E [(σ(u), σ(v)) ̸∈c(e)] and
UNSAT(G) = min
σ
UNSATσ(G) .
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
5
We call UNSAT(G) the unsat-value of G, or just the unsat of G for short. We
deﬁne
size(G)
△= |V | + |E| .
Implicit throughout this paper is the notion that we are working with inﬁnite
families of constraint graphs. In our context the size of the alphabet  will remain
ﬁxed independently of the size of the underlying graph structure, so indeed size(G)
measures the size of the description of G up to a constant multiplicative factor that
depends only on ||.
PROPOSITION 1.6.
Given a constraint graph G = ⟨(V, E), , C⟩with || = 3,
it is NP-hard to decide if UNSAT(G) = 0.
PROOF.
We reduce from graph 3-colorability. Given a graph G, let the alphabet
be = {1, 2, 3}forthethreecolors,andequiptheedgeswithinequalityconstraints.
Clearly, G is 3-colorable if and only if UNSAT(G) = 0.
Observe that in case UNSAT(G) > 0 it must be that UNSAT(G) ≥1/ |G|. There-
fore, it is actually NP-hard to distinguish between the cases (i) UNSAT(G) = 0 and
(ii) UNSAT(G) ≥1/ |G|. Our main theorem is the aforementioned “gap ampliﬁca-
tion step”, where a graph G is converted into a new graph G′ whose unsat value is
doubled.
THEOREM 1.7 (MAIN).
There exists 0 such that the following holds. For any
ﬁnite alphabet  there exist C > 0 and 0 < α < 1 such that, given a constraint
graph G = ⟨(V, E), , C⟩, one can construct, in polynomial time, a constraint
graph G′ = ⟨(V ′, E′), 0, C′⟩such that
—size(G′) ≤C · size(G).
—(Completeness:) If UNSAT(G) = 0 then UNSAT(G′) = 0.
—(Soundness:) UNSAT(G′) ≥min(2 · UNSAT(G), α).
After applying this step logarithmically many times, the ﬁnal outcome Gﬁnal is
a constraint graph for which in case (i) still UNSAT(Gﬁnal) = 0, and in case (ii) we
have UNSAT(Gﬁnal) ≥α for some constant α > 0. Ignoring the fact that instead of
1
2 we got α > 0 (and this can be easily corrected by repetition), this proves the PCP
Theorem (as stated in Theorem 1.3). The formal proof of this is given in Section 3.
Let us describe the ideas which come in to the proof of the main theorem. How do
we make the unsat value double? this is done through three operations on constraint
graphs, which we describe next.
Graph Powering.
In order to amplify the unsat value of a constraint graph we
simply raise it to the power t, for some constant value of t. This operation is a new
operation on constraint systems deﬁned as follows. Let G = ⟨(V, E), , C⟩be a
d-regular constraint graph, and let t ∈N. A sequence (u0, . . . , ut) is called a t-step
walk in G if for all 0 ≤i < t, (ui, ui+1) ∈E. We deﬁne Gt = ⟨(V, E), d⌈t/2⌉, Ct⟩
to be the following constraint graph:
—The vertices of Gt are the same as the vertices of G.
—Edges: u and v are connected by k parallel edges in E if the number of t-step
walks from u to v in G is exactly k.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
6
IRIT DINUR
—Alphabet: The alphabet of Gt is d⌈t/2⌉. The meaning of each value is as follows.
Let (u) = {u′ ∈V |(u = u0, u1, . . . , u⌈t/2⌉= u′) is a walk in G}. Clearly
|(u)| ≤d⌈t/2⌉and by choosing some canonical ordering, a value a ∈d⌈t/2⌉
can be interpreted as an assignment a : (u) →. One may think of this value
as describing u’s opinion of its neighbors’ values.
—Constraints: The constraint associated with an edge e = (u, v) ∈E is satisﬁed by
a pair of values a, b ∈d⌈t/2⌉iff the following holds. There is an assignment σ :
(u)∪(v) → that satisﬁes every constraint c(e) where e ∈E ∩(u)×(v),
and such that
∀u′ ∈(u), v′ ∈(v),
σ(u′) = au′ and σ(v′) = bv′
where au′ is the value a assigns u′ ∈(u), and bv′ the value b assigns v′ ∈(v).
If UNSAT(G) = 0, then clearly UNSAT(Gt) = 0. More interestingly, our main
technical lemma asserts that the unsat value is multiplied by a factor of roughly √t.
This holds as long as the initial underlying graph G is sufﬁciently well structured,
that is, the graph is expanding (captured by bounding λ(G), deﬁned in Section 2.1)
and d-regular for constant d, and has self-loops.
LEMMA 1.8 (AMPLIFICATION LEMMA).
Let 0 < λ < d, and || be constants.
There exists a constant β2 = β2(λ, d, ||) > 0, such that for every t ∈N and
for every d-regular constraint graph G = ⟨(V, E), , C⟩with a self-loop on each
vertex and λ(G) ≤λ,
UNSAT(Gt) ≥β2
√
t · min

UNSAT(G) , 1
t

.
The advantage of the powering operation is that it ampliﬁes the UNSAT value by
factor √t and only incurs a linear blowup in the size of the graph (the number of
edges is multiplied by dt−1).
Preprocessing.
It is quite easy to turn any constraint graph into a ‘well-
structured’ one, as required by the ampliﬁcation step. This can be done with only a
linear blow-up in size, and a constant factor decrease in the unsat value. For exam-
ple, here is a simple way of turning any constant-degree constraint graph into an
expanding one. Simply, take the union of the edges of the given graph with edges
of any constant-degree expander graph on the same set of vertices. Putting null
constraints on the expander edges guarantees that the unsat value only drops by a
constant factor.
The following lemma summarizes the preprocessing step:
LEMMA 1.9 (PREPROCESSING LEMMA).
There exist constants 0 < λ < d and
β1 > 0 such that any constraint graph G can be transformed into a constraint
graph G′, denoted G′ = prep(G), such that
—G′ is d-regular with self-loops, and λ(G′) ≤λ < d.
—G′ has the same alphabet as G, and size(G′) = O(size(G)).
—β1 · UNSAT(G) ≤UNSAT(G′) ≤UNSAT(G).
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
7
Alphabet Reduction by Composition.
The graph powering operation described
above has one drawback: it incurs an increase in the alphabet size. In order to repeat
the ampliﬁcation step many times, the alphabet size must be reduced.
Fortunately, this can be achieved through composition. Composition is an es-
sential component in all PCP constructions, starting with Arora and Safra [1998].
It is most natural in the proof-veriﬁcation setting (rather than as a gap constraint
satisfaction reduction). Recall that a system of q-ary constraints over an alphabet
 corresponds to a probabilistic veriﬁer that reads q symbols from a proof, where
the symbols are taken from .
The basic idea of proof composition is that the veriﬁer, instead of reading the
q symbols from  (of which we think as a ‘large’ alphabet) and based on them
verifying correctness, can delegate this task to another “inner” veriﬁer. This inner
veriﬁer can rely on an additional proof for the fact that this length-q input would
have caused the original veriﬁer to accept. Thus, the veriﬁcation task can potentially
rely on reading even fewer bits than before. Note that there will end up being
many additional proofs, one per random string of the original veriﬁer. Consistency
between these proofs must be ensured, and this well-studied issue will be discussed
in Section 5.
Going back to the language of constraint systems, the “inner veriﬁer” is simply
a reduction transforming a single constraint over large-alphabet variables into a
system of constraints over new small-alphabet variables. This reduction is applied
on every constraint in parallel and is done in a consistent way,1 ensuring that the
UNSAT value of the new system doesn’t drop by more than a constant factor. We
call such a reduction an “assignment tester” and refer the reader to Section 5 and
Deﬁnition 5.2 for a formal deﬁnition of the composition operation.
LEMMA 1.10 (COMPOSITION LEMMA—INFORMAL STATEMENT).
Assume the
existence of an assignment tester P, with constant rejection probability ε > 0,
and alphabet 0, |0| = O(1). There exists β3 > 0 that depends only on P, such
that given any constraint graph G = ⟨(V, E), , C⟩, one can compute, in linear
time, the constraint graph G′ = G ◦P, such that size(G′) = c(P, ||) · size(G),
and
β3 · UNSAT(G) ≤UNSAT(G′) ≤UNSAT(G).
For the sake of self-containedness, we include a construction of an assignment
tester P in Section 7.
1.3. THE COMBINED AMPLIFICATION STEP.
Assuming we have Lemma 1.9,
Lemma 1.8, and Lemma 1.10, the proof of the gap ampliﬁcation step (Theorem 1.7)
is syntactic and is given in Section 3. Altogether, our proof of the PCP theorem
takes the following form: Let G be an instance of constraint graph satisﬁability
(proven NP-hard in Proposition 1.6). Fix t = O(1), set G0 = G, and repeat the
following ampliﬁcation step log |G| times:
(1) Preprocess Gi
(2) Raise the result to the t-th power
(3) Compose the result with an assignment tester reduction P.
1This has to do with the consistency issue mentioned earlier, and will be clariﬁed in Section 5.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
8
IRIT DINUR
In short,
Gi+1 = (prep(Gi))t ◦P
It is not hard to see that taking Gﬁnal = Gi for i = 
(log n) gives the necessary
reduction. Formal details are given in Section 3.
1.4. RELATED WORK.
This work follows Goldreich and Safra [1997] and Dinur
and Reingold [2004] in the attempt to ﬁnd an alternative proof for the PCP Theo-
rem that is combinatorial and/or simpler. In Dinur and Reingold [2004], a quasi-
polynomial PCP Theorem was proven combinatorially. While our proof is different,
we do rely on the modular notion of composition due to Ben-Sasson et al. [2004] and
Dinur and Reingold [2004], and in particular on composition with a bounded-input
assignment-tester, which has already served as an ingredient in the constructions
of Dinur and Reingold [2004].
This construction is inspired by the zig-zag construction of expander graphs due
to Reingold et al. [2002] and by Reingold’s beautiful proof for SL = L [Reingold
2005]. Although there is no direct technical connection between these works and
our construction, our proof has the same overall structure, consisting of a loga-
rithmic number of iterations, where each iteration makes a small improvement in
the interesting parameter (be it the UNSAT value in our case, or the spectral gap in
Reingold’s case).
The steady increase of the UNSAT value is inherently different from the
original proof of the PCP Theorem. There, a constant UNSAT value (using our
terminology) is generated by one powerful transformation, and then a host of
additional transformations are incorporated into the ﬁnal result to take care of
other parameters. Composition is essential in both proofs.
1.5. FURTHER RESULTS.
1.5.1. Short PCPs and Locally Testable Codes.
The goal of achieving ex-
tremely short Probabilistically Checkable Proofs and Locally-Testable Codes
(LTCs) has been the focus of several works [Polishchuk and Spielman 1994;
Harsha and Sudan 2001; Goldreich and Sudan 2002; Ben-Sasson et al. 2003, 2004;
Ben-Sasson and Sudan 2004]. The goal is to convert a standard NP proof into
a “robust” PCP proof, with the minimal amount of increase in the proof length.
Discussion of Locally Testable Codes is deferred to Section 8.
The shortest PCPs/LTCs are due to Ben-Sasson et al. [2004] and Ben-Sasson
and Sudan [2004], each best in a different parameter setting. For the case where
the number of queries is constant, the shortest construction is due to Ben-Sasson
et al. [2004], and the proof-length is n ·2(log n)ε. The construction of Ben-Sasson and
Sudan [2004] has shorter proof-length, n · poly log n, but the number of queries it
requires is poly log n. Our result combines the best parameters from both of these
works. Our starting point is the construction Ben-Sasson and Sudan [2004]. We
ﬁrst transform this construction into a two-query constraint system C whose size is
n · poly log n, such that if the input was a “no” instance, then UNSAT(C) ≥
1
poly log n,
and otherwise UNSAT(C) = 0. Then, by applying our ampliﬁcation step O(log log n)
times, we raise the unsat value to a constant, while increasing the size of the system
by only another polylogarithmic factor. Using standard notation (which is deﬁned
in Section 8), we show that SAT ∈PCP 1
2 ,1[log2(n · poly log n), O(1)].
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
9
1.5.2. Assignment Testers.
We further extend our main ampliﬁcation step
(Theorem 1.7) to work for assignment-tester reductions (alternatively called PCPs
of Proximity), deﬁned in Ben-Sasson et al. [2004] and Dinur and Reingold [2004].
This carries over to extend our combinatorial construction of PCPs to that of
assignment-testers/PCPs of Proximity. Without getting into the full deﬁnition
(which can be found in Section 9) we note that this object is syntactically stronger
than a PCP reduction. It is known to imply the PCP theorem, but the converse is
not known.
We obtain the aforementioned short locally-testable codes by ﬁrst obtaining
short assignment-testers (with comparable parameters to those of the short PCPs
described above), and then applying a simple generic construction from Ben-Sasson
et al. [2004].
1.6. ORGANIZATION.
Section 2 contains some preliminary facts about expander
graphs and probability. In Section 3, we prove the main theorem, relying on
Lemmas 1.8, 1.9, and 1.10 stated above, and deduce the PCP Theorem as well. The
next three sections (Sections 4, 5, and 6) are devoted to the proof of Lemmas 1.9,
1.10 and 1.8, dealing with the three operations on constraint graphs. In Section 7,
we describe a concrete (and inefﬁcient) construction of an assignment-tester P so
as to make our proof self-contained.
Sections 8 and 9 contain the results on short PCPs and LTCs. In Section 8,
we construct PCPs and locally-testable codes whose length is linear up to a poly-
logarithmic factor. In Section 9, we describe how to extend our main ampliﬁcation
step (Theorem 1.7) for assignment-testers. We include a short discussion about our
ampliﬁcation and parallel-repetition in Section 10.
2. Preliminaries
2.1. EXPANDER GRAPHS.
Expander graphs play an important role in a wide
variety of results in theoretical computer science. In this section we will state
some well-known properties of expander graphs. For an excellent exposition to this
subject, we refer the reader to Linial and Wigderson [2003].
Deﬁnition 2.1.
Let G
=
(V, E) be a d-regular graph. Let E(S, ¯S)
=
|(S × ¯S) ∩E| equal the number of edges from a subset S ⊆V to its complement.
The edge expansion of G is deﬁned as
h(G) =
min
S: |S|≤|V |/2
E(S, ¯S)
|S|
.
LEMMA 2.2 (EXPANDERS).
There exist d0 ∈N and h0 > 0, such that there
is a polynomial-time constructible family {Xn}n∈N of d0-regular graphs Xn on n
vertices with h(Xn) ≥h0. (Such graphs are called expanders.)
PROOF.
It is well known that a random constant-degree graph on n-vertices is an
expander. For a deterministic construction, one can get expanders on 2k vertices for
any k from the construction of Reingold et al. [2002]. For n = 2k −n′ (n′ < 2k−1)
one can, for example, merge n′ pairs of non-neighboring vertices. To make this
graph regular one can add arbitrary edges to the nonmerged vertices. Clearly, the
edge expansion is maintained up to a constant factor.
The adjacency matrix of a graph G = (V, E) is a |V | × |V | matrix A such that
Ai j = 1 iff (i, j) ∈E and Aij = 0 otherwise. The second eigenvalue of a graph G,
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
10
IRIT DINUR
denoted λ(G), is the second largest eigenvalue of its adjacency matrix in absolute
value. The Rayleigh quotient gives a convenient expression for this value.
LEMMA 2.3.
Let G be a graph, A its adjacency matrix, and let λ(G) denote
the second largest eigenvalue in absolute value. Then λ(G) = maxx̸=⃗0,x⊥⃗1
|⟨x,Ax⟩|
⟨x,x⟩.
The following important relation between the edge expansion and the second
eigenvalue is well-known, see, for example, Linial and Wigderson [2003],
THEOREM 2.4.
Let G be a d-regular graph with eigenvalues d = λ0 ≥λ1 ≥
· · · ≥λn−1, and let h(G) denote the edge expansion of G. Then
λ1 ≤d −h(G)2
2d
.
As a corollary of Lemma 2.2 and the above theorem, we obtain
COROLLARY 2.5.
There exist d0′ ∈N and 0 < λ0 < d0′, such that there
is a polynomial-time constructible family {Xn}n∈N of d0′-regular graphs Xn on n
vertices with λ(Xn) ≤λ0.
PROOF.
For any n ∈N, let Xn be the d0-regular graph guaranteed by
Lemma 2.2. By adding d0 self-loops to each vertex in Xn, we obtain a d0′ = 2d0-
regular graph X′
n, with the same edge-expansion h0. However, it is easy to see
that now all eigenvalues of X′
n are non-negative, and in particular λ(X′
n) equals
the second-largest eigenvalue of X′
n. Taking λ0 = d0′ −(h0)2
2d0′ < d0′, Theorem 2.4
gives the result.
Finally, we prove the following (standard) estimate on the random-like behavior
of a random-walk on an expander.
PROPOSITION 2.6.
Let G = (V, E) be a d-regular graph with λ(G) = λ. Let
F ⊆E be a set of edges without self loops, and let K be the distribution on vertices
induced by selecting a random edge in F, and then a random endpoint.
The probability p that a random walk that starts with distribution K takes the
i + 1st step in F, is upper bounded by |F|
|E| + ( |λ|
d )i.
PROOF.
Let B ⊆V be the support of K. Let n = |V | and let A be the
normalized n × n adjacency matrix of G, that is, Aij equals k/d where k is the
number of edges between vertices i and j. The ﬁrst and second largest eigenvalues
(in absolute value) of A are 1 and ˜λ = λ/d respectively.
Let x be the vector corresponding to the distribution K, that is, xv = PrK[v]
equals the fraction of edges touching v that are in F, divided by 2. Since the graph
is d-regular, PrK[v] ≤
d
2|F|. Let yv be the probability that a random step from v is
in F, so y = 2|F|
d x. The probability p equals the probability of landing in B after i
steps, and then taking a step inside F,
p =

v∈B
yv(Aix)v =

v∈V
yv(Aix)v = ⟨y, Aix⟩.
Let 1 be the all 1 vector. Write x = x⊥+ x|| where x|| △= 1
n1, is an eigenvector
of A with eigenvalue 1, and x⊥△= x −x||. The vector x⊥is orthogonal to x|| since
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
11
1 · x⊥= 
v PrK[v] −
v
1
n = 1 −1 = 0. Denote ∥x∥=

v x2v. Clearly,
∥Aix⊥∥≤|˜λ|i∥x⊥∥≤|˜λ|i∥x∥.
Observe that ∥x∥2 ≤(
v |xv|) · (maxv |xv|) ≤1 · (maxv |xv|) ≤
d
2|F|. By the
Cauchy–Schwarz inequality,
⟨y, Aix⊥⟩≤∥y∥· ∥Aix⊥∥≤2 |F|
d
∥x∥· |˜λ|i∥x∥≤|˜λ|i .
Combining the above we get the claim,
⟨y, Aix⟩= ⟨y, Aix||⟩+ ⟨y, Aix⊥⟩≤2 |F|
dn
+ |˜λ|i = |F|
|E| +
|λ|
d
i
.
2.2. PROBABILITY.
The following easy fact is a Chebychev-style inequality. It
is useful for showing that for a non-negative random variable X, Pr[X > 0] ≈E[X]
whenever E[X] ≈E[X2].
FACT 2.7.
For any non-negative random variable X ̸≡0, Pr[X > 0] ≥E2[X]
E[X2].
PROOF.
We repeat a proof from O’Donnell and Guruswami [2005, Lecture 5].
E[X] = E [X · 1X>0] ≤

E[X2]

E[(1X>0)2] =

E[X2]

Pr[X > 0].
where we have used the Cauchy–Schwarz inequality. Squaring and rearranging
completes the proof.
2.3. ERROR CORRECTING CODES.
An error-correcting code is a collection of
strings C ⊆n, where  is some ﬁnite alphabet. n is called the block-length of the
code, log|| |C| is the dimension of the code, and 1
n log|| |C| is the rate of the code.
The distance of the code is minx̸=y∈C dist(x, y) where dist(·, ·) refers to Hamming
distance. We also write rdist(x, y) = 1
ndist(x, y) for relative distance.
A one-to-one mapping e : D →n is also sometimes called an error-correcting
code. Its dimension and distance are deﬁned to be the respective dimension and
distance of its image e(D).
It is well known that there exist families of codes {Cn ⊂{0, 1}n}n∈N for which
both the distance and the dimension are 
(n), and for which there is a polynomial-
sized circuit that checks x
?∈Cn, see, for example, Sipser and Spielman [1996].
2.4. ASSIGNMENT TESTER.
An assignment tester is a certain type of PCP trans-
formationthatisusefulforcomposition.Wedescribebelowastripped-downversion
of the deﬁnition of Dinur and Reingold [2004], that sufﬁces for our purposes.
Basically, an assignment tester is an algorithm whose input is a Boolean circuit
 and whose output is a constraint graph G. This graph contains the input variables
of  as some of its vertices, and its unsat value is related to the satisﬁability of 
as follows. Roughly speaking, the only way an assignment for the variables of G
can have a small unsat value is if its restriction to the variables of  is close to an
assignment that satisﬁes . Here is the formal deﬁnition.
For a Boolean circuit  over n variables, denote by SAT() ⊆{0, 1}n the set
of assignments that satisfy .
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
12
IRIT DINUR
Deﬁnition 2.8 (Assignment Tester).
An Assignment Tester with alphabet 0
and rejection probability ϵ > 0 is an algorithm P whose input is a circuit  over
Boolean variables X, and whose output is a constraint graph G = ⟨(V, E), 0, C⟩
such that2 V ⊃X, and such that the following hold. Let V ′ = V \ X, and let
a : X →{0, 1} be an assignment.
—(Completeness) If a ∈SAT(), there exists b : V ′ →0 such that UNSATa∪b
(G) = 0.
—(Soundness)
If a ̸∈SAT() then for all b : V ′ →0, UNSATa∪b(G) ≥
ϵ · rdist(a, SAT()).
Note that we make no requirement on the complexity of the algorithm P.
3. Proofs of the Main Theorem and of the PCP Theorem
Based on the constraint graph operations described in Section 1.2, and on
Lemma 1.9, Lemma 1.8, and Lemma 1.10 we can already prove our main
theorem.
PROOF OF THEOREM 1.7. We deﬁne
G′ = ( prep(G) )t ◦P
for an assignment tester P whose existence is guaranteed by Theorem 5.1, and a
value t ∈N to be determined later. Let us elaborate on the construction of G′:
(1) (Preprocessing step:) Let H1 = prep(G) be the result of applying to G the
transformation guaranteed by Lemma 1.9. There exist some global constants
λ < d and β1 > 0 such that H1 is d-regular, has the same alphabet as G,
λ(H1) ≤λ < d, and β1 · UNSAT(G) ≤UNSAT(H1) ≤UNSAT(G).
(2) (Ampliﬁcation step:) Let H2 = (H1)t, for a large enough constant t > 1 to be
speciﬁed below.
According to Lemma 1.8, there exists some constant β2 = β(λ, d, ||) > 0
for which UNSAT(H2) ≥β2
√t · min(UNSAT(H1), 1
t ). However, the alphabet
grows to d⌈t/2⌉.
(3) (Composition step:) Let G′ = H2 ◦P be the result of applying to H2 the
transformation guaranteed by Lemma 1.10. Here, we rely on the existence of
an assignment tester P, as guaranteed in Theorem 5.1.
Thealphabetof G′ isreducedto0 whilestillβ3·UNSAT(H2) ≤UNSAT(G′) ≤
UNSAT(H2), for a constant β3 > 0.
We now verify the properties claimed above. Completeness is clearly maintained
at each step, that is,
UNSAT(G) = 0 ⇒UNSAT(H1) = 0 ⇒UNSAT(H2) = 0 ⇒UNSAT(G′) = 0.
2 In a constraint graph, the set V plays a double role of both variables and vertices. By V ⊃X, it is
meant that some of the vertices of V are identiﬁed with the X variables.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
13
For soundness, let us choose now
t =

2
β1β2β3
2
,
and
α = β3β2/
√
t.
Altogether,
UNSAT(G′) ≥β3 · UNSAT(H2)
(step 3, Lemma 1.10)
≥β3 · β2
√
t · min

UNSAT(H1), 1
t

(step 2, Lemma 1.8)
≥β3 · β2
√
t · min

β1UNSAT(G), 1
t

(step 1, Lemma 1.9)
≥min(2 · UNSAT(G), α)
Finally, let us verify that each of the three steps incurs a blowup that is linear in the
size of G. In step 1 this is immediate from Lemma 1.9. In step 2, since deg(H1) = d
and t are independent of the size of G, the number of edges in H2 = (H1)t is equal
to the number of edges in H1 times dt−1 (this factor depends on || but that is ﬁne).
In Step (3), the total size grows by a factor c that depends on the alphabet size of
H2, which equals |d⌈t/2⌉|, and on P. Again, both are independent of the size of G.
Altogether, it is safe to write size(G′) ≤C · size(G) where the factor C ultimately
depends only on || and on some global constants.
As a corollary of the main theorem we can immediately prove the PCP theorem,
THEOREM 1.3 (INAPPROXIMABILITY VERSION OF PCP THEOREM).
There are
constants q > 1 and || > 1 such that given a collection C of q-ary constraints over
an alphabet , it is NP-hard to decide whether UNSAT(C) = 0 or UNSAT(C) ≥1
2.
PROOF.
We reduce from constraint graph satisﬁability. According to Proposi-
tion 1.6, it is NP-hard to decide if for a given constraint graph G with || = 3,
UNSAT(G) = 0 or not. So let G be an instance of constraint-graph satisﬁability with
|| = 3, and denote n = size(G). The basic idea is to repeatedly apply the main
theorem until the unsat-value becomes a constant fraction.
Let G0 = G and for i ≥1 let Gi be the result of applying to Gi−1 the trans-
formation guaranteed by Theorem 1.7. Then, for i ≥1 Gi is a constraint graph
with alphabet 0. Let E0 be the edge-set of G0, and let k = log |E0| = O(log n).
Observe that the size of Gi for i ≤k = O(log n) is at most Ci ·size(G0) = poly(n).
Completeness is easy: if UNSAT(G0) = 0, then UNSAT(Gi) = 0 for all i. For
soundness, assume UNSAT(G0) > 0. If for some i∗< k, UNSAT(Gi∗) ≥α/2, then
the main theorem implies that for all i > i∗UNSAT(Gi) ≥α. For all other i, it
follows by induction that
UNSAT(Gi) ≥min(2i UNSAT(G0), α) .
If UNSAT(G0) > 0, then UNSAT(G0) ≥
1
|E0|, so surely 2kUNSAT(G0) > α. Thus,
UNSAT(Gk) ≥α.
This proves that gap constraint satisfaction is NP-hard, for two-variable con-
straints and alphabet size |0|.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
14
IRIT DINUR
To get to a gap between UNSAT(C) = 0 and UNSAT(C) ≥
1
2, one can apply
simple (sequential) repetition u = 1/ log(
1
1−α) = O(1) times. That is, create a new
constraint system C consisting of ANDs of all possible u-tuples of the constraints
in Gk. This creates a system of 2u-ary constraints that has the desired gap.
4. Preprocessing
In this section, we describe how to (rather easily) turn any constraint graph into a
‘nicely structured’ one. We deﬁne a transformation on constraint graphs, taking G
to prep(G) that consists of two simple steps
G →prep1(G) →prep2(prep1(G)).
These transformation are described in Deﬁnitions 4.1 and 4.3 below. The ﬁrst
transformation converts the graph into a constant degree (regular) graph. The second
transformation converts it into an expander. The properties of each transformation
are stated and proved in Lemmas 4.2 and Lemma 4.4 respectively, which together
give an immediate proof for Lemma 1.9.
Deﬁnition 4.1.
Let G = ⟨(V, E), , C⟩be a constraint graph. The constraint
graph prep1(G) = ⟨(V ′, E′), , C′⟩is deﬁned as follows.
—Vertices: For each v ∈V let [v] = {(v, e) | e ∈E is incident on v}, and set
V ′ = ∪v∈v[v].
—Edges: For each v ∈V let Xv be a d-regular graph on vertex set [v] and edge
expansion at least h0 (as guaranteed by Lemma 2.2). Let E1 = ∪v∈V E(Xv) and
set
E2 = {{(v, e), (v′, e)}|e = {v, v′} ∈E}.
Finally let E′ = E1 ∪E2.
—Constraints: The constraints are C′ = {c(e′)}e′∈E′ where c(e′) is deﬁned as fol-
lows:
—If e′ ∈E1, then c(e′) is an equality constraint: c(e′) = {(a, a) | a ∈}.
—If e′ = {(v, e), (v′, e)} ∈E2, then c(e′) = c(e) ∈C.
In words, the constraint graph prep1(G) is obtained from G by blowing up each
vertex into a cloud of as many vertices as its degree. Two clouds are connected by
one edge if the original vertices were adjacent, and the vertices within a cloud are
connected by expander edges. The constraints on external edges (between clouds)
remain the same, and ‘internal’ constraints (within a cloud) enforce equality.
LEMMA 4.2.
Let G = ⟨(V, E), , C⟩be a constraint graph. Then G′ =
prep1(G) is a (d0 + 1)-regular constraint graph G′ = ⟨(V ′, E′), , C′⟩such that
|V ′| ≤2 |E| and
c · UNSAT(G) ≤UNSAT(G′) ≤UNSAT(G)
(1)
for some global constants d0, c > 0.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
15
Moreover, for any assignment σ ′ : V ′ → let σ : V → be deﬁned according
to the plurality value,
∀v ∈V,
σ(v)
△= arg max
a∈
	
Pr
(v,e)∈[v][σ ′(v, e) = a]

.
(2)
Then c · UNSATσ(G) ≤UNSATσ ′(G′).
This lemma relies on a well-known ‘expander-replacement’ transformation due
to Papadimitriou and Yannakakis [1991], and we include a proof for the sake of
completeness.
PROOF.
It is immediate to see that G′ is d = d0+1 regular. Every non-self-loop
edge in E gives rise to two endpoints, so clearly |V ′| ≤2 |E|. We proceed to prove
(1).
The (completeness) upper bound UNSAT(G′) ≤UNSAT(G) is easy: An assign-
ment σ : V → can be extended to an assignment σ ′ : V ′ → by
∀(v, e) ∈V ′,
σ ′(v, e)
△= σ(v).
Clearly σ ′ does not violate the constraints corresponding to edges in E1, and it
violates exactly UNSAT(G) |E2| constraints corresponding to E2. Thus,
UNSAT(G′) ≤
UNSAT(G) |E2|
|E1| + |E2|
≤UNSAT(G).
The (soundness) lower bound c · UNSAT(G) ≤UNSAT(G′) in (1) follows from
the second part of the lemma, which we prove next. The intuitive idea is that the
expander edges “penalize” assignments σ ′ that do not assign the same value to all
copies of v; forcing σ ′ to behave essentially like an assignment σ for G.
Let us ﬁrst observe that
|E′| ≤d |E|
where the inequality would have been equality were there no self-loops in G.
Fix an assignment σ ′ : V ′ →, and let σ : V → be deﬁned according to (2).
In other words, σ(v) is the most popular value among the values occurring in v’s
cloud. Let F ⊆E be the edges of G whose constraints reject σ, and let F′ ⊆E′
be the edges of G′ whose constraints reject σ ′. Let S ⊆V ′ be the set of vertices of
G′ whose value disagrees with the plurality,
S =

v∈V
{(v, e) ∈[v]|σ ′(v, e) ̸= σ(v)} .
Suppose e = {v, v′} ∈F. Then, the edge {(v, e), (v′, e)} either belongs to F′, or
has at least one endpoint in S. Hence, for α
△= |F|
|E| = UNSATσ(G),
|F′| + |S| ≥|F| = α · |E| .
(3)
There are two cases,
—If |F′| ≥
α
2 |E|, we are done since α
2|E| ≥
α
2d |E′| and so UNSATσ ′(G′) ≥
UNSATσ(G)/2d.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
16
IRIT DINUR
—Otherwise, |F′| <
α
2|E|, so by (3), |S| ≥
α
2|E|. Focus on one v, and let
Sv = [v] ∩S. We can write Sv as a disjoint union of sets Sv
a = {(v, e) ∈
Sv|σ ′(v, e) = a}. Since S is the set of vertices disagreeing with the plurality
value, we have |Sv
a| ≤|[v]|/2, so by the edge expansion of the appropriate ex-
pander Xdv, E(Sv
a, [v]\ Sv
a) ≥h0 ·|Sv
a|. All of the edges leaving Sv
a carry equality
constraints that reject σ ′. So there are at least h0
2

v |S ∩[v]| = h0
2 |S| ≥αh0
4 |E|
edges that reject σ ′. Since |E| ≥|E′|/d, we get UNSATσ ′(G′) ≥h0
4d UNSATσ(G).
We have completed the proof, with c = min( 1
2d , h0
4d ).
We now turn to the second transformation, converting a constraint graph into an
expander with self-loops.
Deﬁnition 4.3.
Let G = ⟨(V, E), , C⟩be a constraint graph. The constraint
graph prep2(G) = ⟨(V, E′), , C′⟩is deﬁned as follows.
—Vertices. The vertices remain the same.
—Edges. Let X be a d0′-regular graph on vertex set V and edge set E1, with
λ(X) < λ0 < d0′ (as guaranteed by Corollary 2.5). Let E2 = {{v, v} | v ∈V }.
Finally, let E′ = E ∪E1 ∪E2 (where E′ is a multiset allowing parallel edges).
—Constraints. The constraints are C′ = {c(e′)}e′∈E′ where c(e′) is deﬁned as fol-
lows. If e′ ∈E, then c(e′) is just like before. Otherwise, c(e′) is the null constraint
(always satisﬁed).
LEMMA 4.4.
There are global constants d0′ > λ0 > 0 such that for any d-
regular constraint graph G, the constraint graph G′ = prep2(G) has the following
properties.
—G′ is (d + d0′ + 1)-regular, has a self-loop on every vertex, and λ(G′) ≤d +
λ0 + 1 < deg(G′),
—size(G′) = O(size(G)),
—For every σ : V →,
d
d+d0′+1 · UNSATσ(G) ≤UNSATσ(G′) ≤UNSATσ(G).
PROOF.
Clearly, G′ is d + d0′ + 1-regular and each vertex has a self-loop. To
bound λ(G′), we rely on the Rayleigh quotient (see Lemma 2.3),
λ(G) =
max
∥x∥=1,x⊥⃗1
|⟨x, AGx⟩| ,
where AG is the adjacency matrix of G. Clearly, if we denote adjacency matrix of
X, G′ by AX, AG′ respectively, then AG′ = AG + I + AX, where I is the identity
matrix. Therefore,
λ(G′) =
max
∥x∥=1,x⊥⃗1
|⟨x, AG′x⟩|
≤
max
∥x∥=1,x⊥⃗1
|⟨x, AGx⟩| +
max
∥x∥=1,x⊥⃗1
|⟨x, I x⟩| +
max
∥x∥=1,x⊥⃗1
|⟨x, AXx⟩|
= λ(G) + λ(I) + λ(X) ≤d + 1 + λ0.
Finally, ﬁx σ : V →. Since the new edges are always satisﬁed and since we
increased the total number of edges by at most a factor c′ = d+d0′+1
d
, the fraction
of unsatisﬁed constraints cannot increase, and drops by at most c′.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
17
PROOF OF LEMMA 1.9. Let G′ = prep2(prep1(G)). The lemma is proven with
β1 = c ·
d
d+d0′+1 by quoting Lemmas 4.2 and 4.4.
We conclude with a stronger corollary of Lemmas 4.2 and 4.4 that will be useful
in Section 8.
COROLLARY 4.5.
Let β1 > 0 be the constant from Lemma 1.9. Fix a constraint
graph G, and let G′ = prep(G). Let V be the vertices of G and let V ′ be the vertices
of G′. For any assignment σ ′ : V ′ →, let σ : V → be deﬁned according to
Eq. (2). Then, UNSATσ ′(G′) ≥β1 · UNSATσ(G).
PROOF.
Let G1 = prep1(G) and G2 = prep2(G1). By Lemma 4.4, for every
assignment σ ′ : V ′ →
d
d + d0′ + 1 · UNSATσ ′(G1) ≤UNSATσ ′(G2).
Moreover, by the second part of Lemma 4.2, we see that if we deﬁne σ : V →
according to Eq. (2), then
c · UNSATσ(G) ≤UNSATσ ′(G1).
Combining the two inequalities,
c ·
d
d + d0′ + 1 · UNSATσ(G) ≤
d
d + d0′ + 1 · UNSATσ ′(G1) ≤UNSATσ ′(G2).
Noting that G′ = G2, and that β1 = c ·
d
d+d0′+1 completes the proof.
5. Alphabet Reduction by Composition
In this section, we describe a transformation on constraint graphs that reduces the
alphabet size, while roughly maintaining the unsat-value. We rely on composition,
which is an essential component in the construction of PCPs. To understand com-
position, let us ignore the underlying graph structure of a constraint graph G, and
view it simply as a system of constraints C = {c1, . . . , cm} over a set of variables
X.
Let us step back for a moment and recall our overall goal of proving the PCP
Theorem. What we seek is a reduction from any NP language L to gap constraint
satisfaction. Such a reduction is a polynomial-time algorithm that inputs an instance
x, and generates a system of constraints C with the following gap property: an input
x ∈L translates to a system C for which UNSAT(C) = 0, and an input x ̸∈L
translates to a system C for which UNSAT(C) > α, for some α > 0.
Suppose we have such a “PCP” reduction P that is not necessarily efﬁcient:
the number of constraints P generates may be super-polynomial in its input size.
Nevertheless, suppose the constraints generated by P are always over a small
alphabet 0, with (say) |0| = 8. How would such a “PCP”-reduction P be used
for alphabet reduction?
Let G be a constraint graph with constraints c1, . . . , cm over alphabet . First,
we cast the satisﬁability of each ci as an NP statement, and then we feed it to P. The
output of P is a constraint graph Gi with alphabet size 8. It has the property that if
ci is satisﬁable then so is Gi, and otherwise UNSAT(Gi) ≥α. The ﬁnal constraint
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
18
IRIT DINUR
graph denoted G ◦P would be some form of union of these Gi’s that guarantees
a good relation between the unsat value of G and that of the new graph G ◦P. In
particular, we would like to have the following properties:
—(Perfect Completeness:) If UNSAT(G) = 0, then UNSAT(G ◦P) = 0
—(Soundness:) There is some constant ϵ such that UNSAT(G ◦P) ≥ϵ · UNSAT(G).
There is a subtle issue of consistency which will be discussed shortly below.
Before that, let us convince ourselves that the transformation makes sense in terms
of efﬁciency. Surely, our goal of reducing the size of the alphabet from || to
|0| = 8 has been achieved. What is the size of G ◦P? Note that the size of each
ci that is fed to P can be bounded by some function that depends on ||. Thus,
the size of each Gi can be bounded by another function of || and P, denoted
c(P, ||), that depends on the efﬁciency of P. In our context || remains bounded
as the size of G grows, so asymptotically the output of this procedure is only larger
than the input by a constant factor (with c(P, ||) factoring into the constant).
Consistency.
The soundness property deﬁned above will not be satisﬁed if we
run P on each constraint ci and take the (disjoint) union of the constraint graphs Gi.
It is possible that the system of constraints {c1, . . . , cm} has a non-zero unsat value
that will not carry over to ∪Gi if, say, each constraint ci is satisﬁable on its own. The
problem stems from the fact that we are not interested in the satisﬁability of each ci
but rather in their satisﬁability simultaneously by the same assignment. Therefore,
when we run P on each ci we need a mechanism that causes the assignments for
the various graphs Gi to be “consistent” with each other, that is, to refer to the same
assignment for the original variables.
This issue has been handled before in a modular fashion by making stronger
requirementsonthereductionP.Suchmore-restrictedreductionsarecalledPCPsof
Proximity in Ben-Sasson et al. [2004] or Assignment Testers in Dinur and Reingold
[2004]. Below we repeat Deﬁnition 2.8 of an assignment tester. Essentially, using
an assignment-tester reduction P will force the different constant-size constraint
graphs to have common vertices, and that will ensure consistency. For an exposition
as to why assignment-testers are well-suited for composition, as well as a proof of a
generic composition theorem, see Ben-Sasson et al. [2004] and Dinur and Reingold
[2004].
Deﬁnition 2.8 (Assignment Tester). An Assignment Tester with alphabet 0 and
rejection probability ϵ > 0 is an algorithm P whose input is a circuit  over
Boolean variables X, and whose output is a constraint graph G = ⟨(V, E), 0, C⟩
such that3 V ⊃X, and such that the following hold. Let V ′ = V \ X, and let
a : X →{0, 1} be an assignment.
—(Completeness) If a ∈SAT(), there exists b : V ′ →0 such that UNSATa∪b
(G) = 0.
—(Soundness) If a ̸∈SAT(), then for all b : V ′ →0, UNSATa∪b(G) ≥
ϵ · rdist(a, SAT()).
3 In a constraint graph, the set V plays a double role of both variables and vertices. By V ⊃X, it is
meant that some of the vertices of V are identiﬁed with the X variables.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
19
We remark that our deﬁnition of the rejection probability is stronger than the stan-
dard deﬁnition in the literature. Here, it is really the ratio between the the probability
of rejection and the distance of the given assignment from a satisfying one.
We prove in Section 7 that such an object exists:
THEOREM 5.1.
There is some ϵ > 0 and an explicit construction of an assign-
ment tester P with alphabet 0 = {0, 1}3 and rejection probability ϵ.
Notice that no statement was made on the running time of P, and none will be
necessary.
Let us now deﬁne the composition between a constraint graph G and an as-
signment tester P. The deﬁnition requires an auxiliary error correcting code
e :  →{0, 1}ℓ. We recall the following standard deﬁnitions. An error correcting
code is said to have linear dimension if there is some constant c > 0 such that
ℓ≤c · log2 . It is said to have relative distance ρ > 0 if for every a1 ̸= a2 ∈,
the strings e(a1) and e(a2) differ on at least ρℓbits, namely rdist(e(a1), e(a2)) ≥ρ.
Two ℓ-bit strings s1, s2 are said to be δ-far (respectively, δ-close) if rdist(s1, s2) ≥δ
(respectively, if rdist(s1, s2) ≤δ).
Deﬁnition 5.2 (Composition).
Let G = ⟨(V, E), , C⟩be a constraint graph
and let P be an assignment tester. Let e :  →{0, 1}ℓbe an arbitrary encoding
with linear dimension and relative distance ρ > 0. The constraint graph G ◦P =
⟨(V ′, E′), 0, C′⟩is deﬁned in two steps.
(1) Robustization: First, we convert each constraint c(e) ∈C to a circuit ˜c(e) as
follows.Foreachvariablev ∈V ,let[v]beafreshsetofℓBooleanvariables.For
each edge e = (v, w) ∈E, ˜c(e) will be a circuit on 2ℓBoolean input variables
[v] ∪[w]. The circuit ˜c(e) will output 1 iff the assignment for [v] ∪[w] is the
legal encoding via e of an assignment for v and w that would have satisﬁed c.
(2) Composition: Run the assignment tester P on each ˜c(e). Let Ge
=
⟨(Ve, Ee), 0, Ce⟩denote the resulting constraint graph, and recall that [v] ∪
[w] ⊂Ve. Assume, wlog, that Ee has the same cardinality for each e. Finally,
deﬁne the new constraint graph G ◦P = ⟨(V ′, E′), 0, C′⟩, by
V ′ =

e∈E
Ve,
E′ =

e∈E
Ee,
C′ =

e∈E
Ce .
Our main lemma in this section is the following,
LEMMA 1.10 (COMPOSITION). Assume the existence of an assignment tester P,
with constant rejection probability ε > 0, and alphabet 0, |0| = O(1). There
exist a constant β3 > 0 that depends only on P, and a constant c(P, ||) that
depends only on P and ||, such that the following holds. Given any constraint
graph G = ⟨(V, E), , C⟩, one can compute, in time that is linear in size(G), the
constraint graph G′ = G ◦P, such that size(G′) = c(P, ||) · size(G), and
β3 · UNSAT(G) ≤UNSAT(G′) ≤UNSAT(G).
PROOF.
First, let us verify that G′ = G ◦P can be computed in time linear
in size(G). The ﬁrst step (robustization) consists of |E| steps of converting c(e) to
a circuit ˜c(e). This circuit computes a Boolean function on 2ℓBoolean variables.
Thus, each conversion can clearly be done in time 2O(ℓ), which is a factor that
depends ultimately only on || and not on size(G). In the second step, we feed each
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
20
IRIT DINUR
˜c(e) to P, obtaining the constraint graph Ge. Even if the running time of P is huge
compared to its input length, this makes no difference. The reason is that the size of
the input to P is bounded by some absolute constant, again depending on ||, and
therefore the size of the output is bounded by some other absolute constant (which
equals the maximal output length ranging over all of the ﬁnitely many different
inputs). Since the blowup factor depends only on || and on P we can write
size(G′) = c(P, ||) · size(G).
It remains to be seen that β3 · UNSAT(G) ≤UNSAT(G′) ≤UNSAT(G). The proof
is straightforward and follows exactly the proof of the composition theorem in
Dinur and Reingold [2004].
Let us start with the easy part of proving UNSAT(G′) ≤
UNSAT(G). Let
σ : V → be an assignment for G such that UNSAT(G) = UNSATσ(G). We
construct an assignment σ ′ : V ′ →0 by following the two steps in Deﬁnition 5.2.
Recall that each vertex v was replaced by a set of vertices [v]. For each v ∈V , we set
σ ′([v]) = e(σ(v)) ∈{0, 1}ℓ
where σ ′([v]) means the concatenation of σ ′(y) for all y ∈[v]. It remains to deﬁne
values for σ ′ on

e=(u,v)∈E
(Ve \ ([u] ∪[v]).
If e = (u, v) ∈E is such that c(e) is satisﬁed by σ, then by deﬁnition the circuit
˜c(e) is satisﬁed by σ ′ restricted to [u] ∪[v]. Then, according to the completeness
property of P, there is an extension assignment for Ve \ ([u] ∪[v]) that satisﬁes all
constraints in Ge. In other words, if we let a denote the restriction of σ ′ to [u]∪[v],
then there is some b : Ve \ ([u] ∪[v]) →0 such that UNSATa∪b(Ge) = 0. Deﬁne
σ ′ to coincide with b on Ve \ ([u] ∪[v]).
For the remaining vertices (belonging to graphs Ge whose constraint c(e) is
unsatisﬁed by σ) deﬁne σ ′ arbitrarily. Since each Ee has the same cardinality, it
is easy to see that UNSATσ ′(G′) ≤UNSATσ(G). Therefore,
UNSAT(G′) ≤UNSATσ ′(G′) ≤UNSATσ(G) = UNSAT(G).
We now move to the left inequality: β3 · UNSAT(G) ≤UNSAT(G′). We need
to prove that every assignment for G′ violates at least β3 · UNSAT(G) fraction of
G′’s constraints. So let σ ′ : V ′ →0 be a best assignment for G′, i.e., such that
UNSATσ ′(G′) = UNSAT(G′). We ﬁrst extract from it an assignment σ : V →
for G by letting, for each v ∈V , σ(v) be a value whose encoding via e is closest
to σ ′([v]). Let F ⊆E be the edges of G whose constraints are falsiﬁed by σ. By
deﬁnition, |F|
|E| = UNSATσ(G) ≥UNSAT(G). Now let e = (u, v) ∈F. We will show
that at least a β3 fraction of the constraints of the graph Ge are falsiﬁed by σ ′.
Recall that the constraint graph Ge is the output of P on input ˜c(e). Thus, we must
analyze the distance of the assignment for [u] ∪[v] from the set SAT(˜c(e)) of
assignments that satisfy ˜c(e). The main observation is that the restriction of σ ′ to
[u] ∪[v], is at least ρ/4-far from SAT(˜c(e)) (where ρ denotes the relative distance
of e). The reason is the deﬁnition of σ(u) (respectively, σ(v)) as the value whose
encoding is closest to σ ′([u]) (respectively, σ ′([v])). This means that at least a ρ/2
fraction of the bits in either [u] or [v] (or both) must be changed in order to change
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
21
σ ′ into an assignment that satisﬁes ˜c(e). So
rdist( σ ′|[u]∪[v], SAT(˜c(e)) ) ≥ρ/4.
By the soundness property of P, at least ε · ρ/4 = (1) fraction of the
constraints in Ge are unsatisﬁed, and we set β3 = ερ/4 > 0. Altogether,
UNSAT(G′) = UNSATσ ′(G′)
=
1
|E|

e∈E
UNSATσ ′|Ve(Ge)
≥
1
|E|

e∈F
UNSATσ ′|Ve(Ge)
≥β3
|F|
|E| = β3UNSATσ(G) ≥β3UNSAT(G),
where the second equality follows since |Ee| is the same for all e ∈E.
6. Ampliﬁcation Lemma
In this section we prove the ampliﬁcation lemma. In fact, we prove the follow-
ing slightly stronger lemma from which Lemma 1.8 follows as an immediate
corollary.
LEMMA 6.1.
Let λ < d, and || be arbitrary constants. There exists a constant
β2 = β2(λ, d, ||) > 0, such that for every t ∈N and for every d-regular constraint
graph G = ⟨(V, E), , C⟩with self-loops and λ(G) ≤λ the following holds. For
every ⃗σ : V →d⌈t/2⌉let σ : V → be deﬁned according to “popular opinion”
by setting, for each v ∈V ,
σ(v)
△= max arga∈ {Pr[A random ⌈t/2⌉-step walk
from v reaches a vertex w for which ⃗σ(w)v = a]} .
(4)
where ⃗σ(w)v ∈ denotes the restriction of ⃗σ(w) to v. Then,
UNSAT⃗σ(Gt) ≥β2
√
t · min

UNSATσ(G) , 1
t

.
Throughout this section all constants, including those implicitly referred to by
O(·) and (·) notation, are independent of t but may depend on d, λ and ||. Also,
let us assume for notational clarity that t is even.
Before we move to the proof of Lemma 6.1, let us see how it yields Lemma 1.8.
PROOF OF LEMMA 1.8. Let ⃗σ an assignment for Gt with minimum unsat value.
Then, for σ deﬁned according to (4),
UNSAT(Gt) = UNSAT⃗σ(Gt) ≥β2
√
t · min

UNSATσ(G) , 1
t

≥β2
√
t · min

UNSAT(G) , 1
t

where the ﬁrst inequality is due to Lemma 6.1.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
22
IRIT DINUR
Let us provide some intuition for why Lemma 6.1 holds. Let us begin by a
simple mental experiment. Fix an assignment σ : V → for G, and consider
the probability of choosing t edges in G independently at random and checking
whether σ falsiﬁes at least one of these edges. This probability is roughly t times
larger than UNSATσ(G). Moreover, since G is an expander graph, the probability
remains (roughly) the same even if the t edges are chosen by taking a random
length-t walk in G.
The graph Gt is constructed to simulate this behavior. It is not hard to see that
if ⃗σ : V →dt/2 were “faithful” to some underlying assignment σ : V →
(i.e., ⃗σ(v)w = σ(w) for each w reachable from v by t/2 steps) then UNSAT⃗σ(Gt)
is lower-bounded by the result of the mental experiment. The proof of Lemma 6.1
is more tricky since we must consider assignments ⃗σ that are not “faithful” to any
underlying assignment.
The idea of the proof is as follows: Let us refer to the edges of Gt as walks,
since they come from t-step walks in G, and let us refer to the edges of G as
edges. Given an assignment for Gt, ⃗σ : V →dt/2, we extract from it a new
assignment σ : V → by assigning each vertex v the most popular value among
the “opinions” (under ⃗σ) of v’s neighbors. We then relate the fraction of edges
falsiﬁed by this “popular-opinion” assignment σ to the fraction of walks falsi-
ﬁed by ⃗σ. The probability that a random edge rejects this new assignment is, by
deﬁnition, at least UNSAT(G). The idea is that a random walk passes through at
least one rejecting edge with even higher probability. Moreover, we will show
that if a walk does pass through a rejecting edge, it itself rejects with constant
probability.
PROOF OF LEMMA 6.1. Let ⃗σ : V →dt/2 be any assignment for Gt. For each
v, ⃗σ(v) assigns a vector of dt/2 values in , interpreted as values for every vertex
w within distance t/2 of v. This can be thought of as the opinion of v about w.
Deﬁne the assignment σ : V → according to (4). Let Xv be a random variable
that assumes a value a with probability that a t/2-step random walk from v ends
at a vertex w for which ⃗σ(w)v = a. Then, σ(v) = a for a value a that maximizes
Pr[Xv = a], and in particular
Pr[Xv = σ(v)] ≥
1
||.
(5)
As mentioned above, the assignment σ can be interpreted as being the “popular
opinion” about v among v’s neighbors.
Let F be a subset of edges that reject σ so that if UNSATσ(G) < 1/t, then
|F|
|E| = UNSATσ(G), and otherwise we take F to be an arbitrary subset of these
edges, such that |F| = ⌊|E|
t ⌋. We have
|F|
|E| ≤min(UNSATσ(G), 1/t),
(6)
where equality holds if we ignore the rounding error. From now on ⃗σ, σ, F will be
ﬁxed for the rest of the proof.
Let E = E(Gt) be the edge set of Gt. There is a one-to-one correspondence
between edges e ∈E and walks of length t in G. With some abuse of notation, we
write e = (v0, v1, . . . , vt) where (vi−1, vi) ∈E for all 1 ≤i ≤t.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
23
Deﬁnition 6.2.
A walk e = (v0, . . . , vt) ∈E is hit by its ith edge if
(1) (vi−1, vi) ∈F, and
(2) Both ⃗σ(v0)vi−1 = σ(vi−1) and ⃗σ(vt)vi = σ(vi).
Let
I =

t
2 −

t
2 < i ≤t
2 +

t
2

⊂N
be the set of “middle” indices. For each walk e, we deﬁne N(e) to be the number
of times e is hit in its middle portion:
N(e) = |{i ∈I | e is hit by its ith edge}| .
N(e) is an integer between 0 and
√
2t. Clearly, N(e) > 0 implies that e rejects under
⃗σ (because having e hit by the ith edge means (vi−1, vi) ∈F and so σ(vi−1) is in-
consistent with σ(vi) which carries over to the constraint on ⃗σ(v0) and ⃗σ(vt)). Thus,
Pr
e [N(e) > 0] ≤Pr
e [e rejects ⃗σ] = UNSAT⃗σ(Gt) .
We will prove
(
√
t) · |F|
|E| ≤Pr
e [N(e) > 0] .
(7)
Combining the above with (6) we get
(
√
t) · min

UNSATσ(G), 1
t

≤(
√
t) · |F|
|E| ≤Pr
e [N(e) > 0] ≤UNSAT⃗σ(Gt),
which gives the lemma.
We will prove (7) by estimating the ﬁrst and second moments of the random
variable N,
LEMMA 6.3
Ee[N(e)] ≥(
√
t) · |F|
|E|.
LEMMA 6.4
Ee[(N(e))2] ≤O(
√
t) · |F|
|E|.
Equation (7) follows by Fact 2.7,
Pr[N(e) > 0] ≥E2[N(e)]/E[(N(e))2] = (√t) · |F|
|E|.
6.1. PROOF OF LEMMA 6.3.
Deﬁne an indicator variable Ni by setting Ni(e) = 1
iff the walk e is hit by its ith edge, as in deﬁnition 6.2. Recall
I =

t
2 −

t
2 < j ≤t
2 +

t
2

.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
24
IRIT DINUR
Clearly, N = 
i∈I Ni. In order to estimate E[N] we will estimate E[Ni], and use
linearity of expectation.
Fix i ∈I. In order to estimate E[Ni] we choose e ∈E according to the following
distribution:
(1) Choose e = (u, v) ∈E uniformly at random.
(2) Choose a random walk of length i −1 starting from u, denote it by (u =
vi−1, vi−2, . . . , v1, v0).
(3) Choose a random walk of length t −i starting from v, denote it by (v =
vi, vi+1, . . . , vt).
(4) Output the walk e = (v0, . . . , vt).
Since G is d-regular this is no other than the uniform distribution on E. According
to Deﬁnition 6.2, e is hit by its ith edge iff (u, v) ∈F and ⃗σ(v0)u = σ(u) and
⃗σ(vt)v = σ(v).
Clearly, the probability that Step (1) results in an edge (u, v) ∈F equals exactly
|F|
|E|. Observe also that the choice of v0 in Step (2) only depends on u, and the choice
of vt in Step (3) only depends on v. Therefore,
Pr[Ni > 0] = |F|
|E| · pu · pv,
(8)
where pu = Prv0[⃗σ(v0)u = σ(u)] and pv = Prvt[⃗σ(vt)v = σ(v)]. It remains to
analyze pu and pv. Let us focus on pu as the case of pv is symmetric.
Deﬁne a random variable Xu,ℓas follows. Xu,ℓtakes a value a ∈ with proba-
bility that a random ℓ-step walk from u ends in a vertex w for which ⃗σ(w)u = a. In
these terms pu = Pr[Xu,i−1 = σ(u)], (and pv = Pr[Xv,t−i = σ(v)]). Recall that by
deﬁnition σ(u) equals a value a ∈ that maximizes Pr[Xu,t/2 = a]. In particular,
Pr[Xu,t/2 = σ(u)] ≥
1
||. For i −1 = t/2, it follows immediately that pu ≥1/ ||.
We will prove that for all ℓ
If
|ℓ−t/2| ≤

t/2
then
Pr[Xu,ℓ= a] > τ
2 · Pr[Xu,t/2 = a]
(9)
for some absolute constant τ > 0 to be determined. The intuition for (9) is that
the self-loops of G make the distribution of vertices reached by a random t/2-step
walk from u roughly the same as distribution on vertices reached by an ℓ-step walk
from u, for any ℓ∈I.
Fix ℓ∈I. Mark one self-loop on each vertex, and observe that any length-ℓ
walk from u in G can be equivalently described by (i) specifying in which steps
the marked edges were traversed, and then (ii) specifying the remaining steps
conditioned on choosing only non-marked edges. Let X′
u,k be a random variable
that assumes a value a with probability that a k-step random walk conditioned on
walking only on nonmarked edges reaches a vertex w for which ⃗σ(w)u = a. In
other words, for a binomial variable Bℓ,p with Pr[Bℓ,p = k] =
ℓ
k

pk(1−p)ℓ−k and
p = 1 −1/d,
Pr[Xu,ℓ= a] =
ℓ

k=0
Pr[Bℓ,p = k] Pr[X′
u,k = a] .
(10)
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
25
The point is that if |ℓ1 −ℓ2| is small, then the distributions Bℓ1,p and Bℓ2,p are
similar, as formalized in the following lemma:
LEMMA 6.5.
For every p ∈(0, 1) and c > 0 there exists some ℓ0 > 0 and
0 < τ < 1 such that if ℓ0 < ℓ1 −√ℓ1 ≤ℓ2 < ℓ1 + √ℓ1, then
∀k, |k −pℓ1| ≤c

ℓ1,
τ ≤Pr[Bℓ1,p = k]
Pr[Bℓ2,p = k] ≤1
τ .
The proof is a straightforward computation that follows from concentration prop-
erties of the binomial distribution, and can be found in Appendix A. We choose
c > 0 so that
K = {k ∈N||k −pt/2| ≤c

t/2}
islarge:Prk∼Bt/2,p[k ̸∈K] < 1/(2 ||).Then,weapplyLemma6.5withtheconstant
c > 0, p = 1 −1
d , ℓ1 = t/2, and ℓ2 = ℓand deduce for all k ∈K,
Pr[Bℓ,p = k] ≥τ · Pr

B t
2 ,p = k

,
where 0 < τ < 1 is the appropriate constant from the lemma.
We now have for any ℓ∈I,
Pr[Xu,ℓ= a] ≥

k∈K
Pr[Bℓ,p = k] Pr[X′
u,k = a]
≥τ ·

k∈K
Pr[Bt/2,p = k] Pr[X′
u,k = a]
≥τ ·

Pr[Xu,t/2 = a] −
1
2 ||

≥τ
2 · Pr[Xu,t/2 = a]
where the last inequality holds because of (5). This establishes (9), and so pu, pv >
τ/(2 ||) because both i −1, t −i are at most √t/2 away from t/2. Plugging
this into Eq. (8), we get E[Ni] ≥|F|/|E| · (1), and this completes the proof of
Lemma 6.3.
6.2. PROOF OF LEMMA 6.4.
For a walk e, let ei denote its ith edge. In order to
upper bound Ee[N(e)2] (all expectations are taken over uniform choice of e), we
deﬁne a random variable Z(e) = |{i ∈I | ei ∈F}| that counts how many times e
intersects F in the middle portion recall
I =

t
2 −

t
2 < j ≤t
2 +

t
2

.
Clearly, 0 ≤N(e) ≤Z(e) for all e, so we will bound E[N(e)2] using E[N(e)2] ≤
E[Z(e)2].
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
26
IRIT DINUR
Let Zi = Zi(e) be an indicator random variable that is 1 iff ei ∈F. So Z(e) =

i∈I Zi(e), and by linearity of expectation,
Ee[Z(e)2] =

i, j∈I
Ee[Zi(e)Z j(e)]
=

i∈I
E[Zi] + 2

i < j
i, j ∈I
E[Zi Z j]
= |I| |F|
|E| + 2

i < j
i, j ∈I
E[Zi Z j].
(11)
As it turns out, E[Z2] is not much larger than |I| |F|/|E| ≈√t|F|/|E|. The
intuitive reason is that since the graph G is an expander, correlations between the
ith and the jth steps of a random walk cannot last long, so  E[Zi Z j] is small.
PROPOSITION 6.6.
Fix i, j ∈I, i < j, and F ⊆E. Then,
E[Zi Z j] ≤|F|
|E|
|F|
|E| + |λ| j−i−1

.
Let us ﬁrst see that combining the proposition with (11) completes the lemma.
Indeed, since |I| =
√
2t and since |F|
|E| ≤1
t ,

i < j
i, j ∈I
E[Zi Z j] ≤|F|
|E|

i < j
i, j ∈I
|F|
|E| + |λ| j−i

< |I|2
|F|
|E|
2
+ |I| |F|
|E|
√
2t

i=1
|λ|i
= O(
√
t) · |F|
|E|,
where the ‘O’ notation is hiding a constant that depends only on |λ|. Let us now
prove the proposition.
PROOF.
Observe that Zi Z j ∈{0, 1}, and Pr[Z j = 1] = |F|
|E|. Thus,
E[Zi Z j] = Pr[Zi Z j = 1] = Pr[Zi = 1] Pr[Z j = 1 | Zi = 1]
= |F|
|E| · Pr[Z j = 1 | Zi = 1].
Assume ﬁrst i = 1 and j > i. By Proposition 2.6,
Pr
e [Z j(e) = 1 | Z1(e) = 1] ≤|F|
|E| + |λ| j−2 ,
where λ < 1 is the normalized second eigenvalue of the graph G. Indeed, let
e = (v0, . . . , vt), conditioned on Z1(e) = 1 the distribution of v1 is exactly the
distribution K deﬁned in Proposition 2.6, so the probability that the j-th edge in
this walk is in F is at most |F|
|E| + ( |λ|
d ) j−2.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
27
If j > i > 1, we don’t care where the random walk e visited during its ﬁrst i −1
steps, so we can ignore those steps. In other words, the last t −i + 1 steps of a
random walk of length t are a random walk of length t −i + 1. This is formalized
by writing
Pr
|e|=t[Z j(e) = 1 | Zi(e) = 1] =
Pr
|e′|=t−i+1[Z j−i+1(e′) = 1 | Z1(e′) = 1] .
Now, by applying Proposition 2.6 on walks of length t −i + 1, the right-hand side
cannot exceed |F|
|E| + |λ| j−i−1.
We conclude this section by commenting that there is a modiﬁcation of our
construction, due to Jaikumar Radhakrishnan, that allows one to replace √t in
Lemma 1.8 by t. This is obviously tight (up to the constant hidden in the O notation).
Ampliﬁcation by factor 
(t) is achieved by the following modiﬁed deﬁnition of
Gt: the vertices stay the same, and the alphabet is dt/2 as before. The edges
of Gt are weighted, and described by the following random process: choose a
vertex v at random and choose a second vertex by taking a random walk form
v that stops after each step with probability 1/t. The constraints are deﬁned as
before. For details on how to analyze this construction, the reader is referred to
Radhakrishnan [2006].
7. An Explicit Assignment Tester
In this section, we prove Theorem 5.1, that is, we outline a construction of an
assignment tester P. Let ψ be a Boolean circuit over Boolean variables x1, . . . , xs.
We describe an algorithm P whose input is ψ and whose output will be a constraint
graph satisfying the requirements of Deﬁnition 2.8. We begin by introducing the
Long-Code. Let
L = { f : {0, 1}s →{0, 1}}
be the set of all Boolean functions on s bits. Given a string a = (a1, . . . , as) ∈
{0, 1}s, deﬁne Aa : L →{0, 1} by
∀f ∈L
Aa( f ) = f (a) .
(12)
Each Aa itself can be viewed as a string of |L| bits, and the set of strings
{Aa | a ∈{0, 1}s} is an error-correcting code called the Long-Code. Recall that
two ℓ-bit strings s1, s2 are said to be δ-far (respectively, δ-close) from one another
if dist(s1, s2) ≥δℓ(respectively, if dist(s1, s2) ≤δℓ). It is not hard to see that, if
a ̸= a′, then Aa and Aa′ are 1
2-far from one another.
In fact we consider only so-called “folded” strings. A string A is said to be folded
over true if for every f , A(−f ) = −A( f ). A string A is said to be folded over
ψ : {0, 1}s →{0, 1} if for every f , A( f ) = A( f ∧ψ). When ψ is clear from the
context we say that a string A is “folded” if it is folded both over true and over ψ.
Clearly, in order to specify a folded string A : L →{0, 1} it is enough to specify
it on the coordinates L′
ψ ⊂L, deﬁned as follows. For every pair f, 1 −f ∈L, let
L′ contain exactly one of them, and set
L′
ψ = { f ∈L′ | f = f ∧ψ}.
We are now ready to state the Long-Code test theorem.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
28
IRIT DINUR
THEOREM 7.1.
There exists a Long-Code Test T which is a randomized algo-
rithm that has input a function ψ : {0, 1}s →{0, 1}, and also oracle access to
a folded string A : L →{0, 1}. T reads the input ψ and tosses some random
coins. Based on these, it computes a three-bit predicate w : {0, 1}3 →{true, false}
and three locations f1, f2, f3 ∈L in which it queries the string A. It then outputs
w(A( f1), A( f2), A( f3)). Denote an execution of T with access to input ψ and string
A by T A(ψ). Then, the following hold,
—Perfect completeness: If a ∈{0, 1}s such that ψ(a) = 1, then Pr[T Aa(ψ) =
true] = 1.
—Strong4 soundness: For every δ ∈[0, 1], if A : L →{0, 1} is folded and at least
δ-far from Aa for all a for which ψ(a) = 1, then Pr[T A(ψ) = false] ≥(δ).
Forthesakeofself-containedness,weincludeaproofofthistheoreminAppendixB.
We now proceed to construct a system of constraints based on the test T . This is
done in two rather standard steps,
(1) Modiﬁed Test: Let X = {x1, . . . , xs} be a set of s Boolean variables. Also, let
there be a Boolean variable for each f ∈L′
ψ. Since an assignment for these
variables can be expanded into a folded assignment for L, we pretend from
now on that we have a Boolean variable for every f ∈L. We allow the test to
access any variable indexed by L. When it accesses some variable f ∈L \ L′
ψ
the value of the variable is determined by accessing the appropriate variable in
L′
ψ. For example, if 1−f ∈L′
ψ then to read the value of f we access the value
of 1 −f and negate the assignment. To summarize, from now on we ignore
this issue and simply pretend that we have a variable for each f ∈L and that
the assignment for these variables is guaranteed to be folded.
Deﬁne a modiﬁed test T ′ as follows: Given input ψ and oracle access to a
folded assignment A : L →{0, 1} and an assignment σ : X →{0, 1}, run T
on ψ and A with probability 1/2, and otherwise choose a random xi ∈X and
a random f ∈L, and test that σ(xi) = A( f ) ⊕A( f + ei).
(2) Creating the Constraints: Introduce a new variable zr per outcome r of the coin
tosses of T ′. These variables will take values in {0, 1}3, supposedly specifying
the correct values of all three variables queried by T ′ on coin tosses r.
We construct the following system of constraints: There will be a constraint
for every possible choice of zr ∈Z and a variable y of the three accessed by T ′
on coin toss r (so y ∈X ∪L). This constraint will check that the assignment for
zr would have satisﬁed T ′, and that it is consistent with the assignment for y.
The algorithm P will output the constraint graph G whose vertices are X ∪L ∪Z,
and whose constraints (and edges) are as speciﬁed above. The alphabet is 0 =
{0, 1}3, where the Boolean variables X ∪L take values only in {000, 111} ⊂0,
identiﬁed with {0, 1} (i.e., a constraint involving y ∈X ∪L immediately rejects if
the value of y is not in {000, 111}).
LEMMA 7.2.
The reduction taking ψ : {0, 1}s →{0, 1} to G is an assignment
tester, with 0 = {0, 1}3 and constant rejection probability ε > 0.
4 We refer to “strong” soundness as opposed to regular soundness, due to the stronger property of
having the rejection probability proportional to the distance from a “good” string.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
29
PROOF.
Let us identify the Boolean variables of ψ with X, so the constraint
graph G has the correct form according to Deﬁnition 2.8. We need to prove
—(Completeness) If a ∈SAT(ψ), there exists b : L∪Z →0 such that UNSATa∪b
(G) = 0.
—(Soundness) If a ̸∈SAT(ψ), then for all b : L ∪Z →0, UNSATa∪b(G) ≥
ϵ · rdist(a, SAT(ψ)).
The completeness part is easy. Let the assignment for the variables in L be Aa
(deﬁned in Eq. (12)). It is then easy to assign the variables Z in a consistent manner.
For soundness, assume that σ : X →{0, 1} is an assignment such that
rdist(σ, SAT(ψ)) = δ, for some δ > 0. Fix any b : L ∪Z →0, and denote
A = b|L. We claim
PROPOSITION 7.3.
Pr[T ′ A,σ(ψ) = false] = (δ).
PROOF.
Weobservethat A isfolded(bythediscussioninitem1above). Assume
ﬁrst that A : L →{0, 1} is δ/2 far from Aa for all a ∈SAT(ψ) ⊂{0, 1}s. Then, by
Theorem 7.1 T rejects with probability at least (δ), so T ′ rejects with probability
at least half of that, which is also (δ). Otherwise, A is δ/2-close to the long-
code encoding of some a′ ∈SAT(ψ). We now compare a′ and σ which are both
assignments for the variables of ψ. Since a′ ∈SAT(ψ),
Pr
i [σ(xi) ̸= a′(xi)] = rdist(σ, a′) ≥rdist(σ, SAT(ψ)] = δ.
Now recall that with probability 1/2, T ′ chooses a random i and a random f and
checks that A( f ) ⊕A( f + ei) = σ(xi). Since A is δ
2-close to Aa′, we have for all i:
Pr
f ∈L[A( f ) ⊕A( f + ei) = a′(xi)] ≥Pr
f ∈L[A( f ) = f (a′)
and
A( f + ei) = ( f ⊕ei)(a′)]
≥1 −2 · δ/2 = 1 −δ
The check fails whenever i, f are such that a′(xi) ̸= σ(xi) and yet A( f ) ⊕A( f +
ei) = a′(xi). Altogether this occurs with probability at least (1 −δ)δ ≥δ/2, and
T ′ runs this test with probability 1/2, so it rejects again with probability (δ) as
claimed.
Consider the assignment b|Z. For every random string that causes T ′ to reject
(on input σ, A), the associated variable zr is either assigned consistently with A, σ
which means that its value immediately causes the associated constraint to reject;
or it is inconsistent with A, σ. Each inconsistency will be detected with probability
at least 1/3. Thus at least (δ)
3
= (δ) fraction of the constraints reject. Hence,
UNSATa∪b(G) = (δ) = (rdist(σ, SAT(ψ))).
8. Short PCPs and Locally Testable Codes
In this section, we describe how to construct extremely short Probabilistically
Checkable Proofs and Locally-Testable Codes (LTCs). Our starting point is the
construction of Ben-Sasson and Sudan [2004]. The case of short PCPs follows
rather directly from our main theorem (Theorem 1.7) and is described ﬁrst, in Sub-
section 8.2. The case of short LTCs is analogous, and is obtained similarly from a
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
30
IRIT DINUR
variant of the main theorem. This variant is an adaptation of our reduction between
constraint graphs into a special kind of reduction called an assignment tester or a
PCP of Proximity. We feel that this adaptation may be of independent interest, and
it is described fully in Section 9. Assuming this adaptation, we describe our short
LTCs in Subsection 8.3. Let us ﬁrst begin with some deﬁnitions and notations.
8.1. DEFINITIONS AND NOTATION.
Given a system of constraints , we denote
its unsat-value by UNSAT(): the minimum over all possible assignments for ’s
variables, of the fraction of unsatisﬁed constraints. This is a natural extension of
the unsat-value of a constraint graph.
Deﬁnition 8.1 (PCPs,c[log ℓ, q]).
We
deﬁne
the
class
of
languages
PCPs,c[log2(ℓ(n)), q(n)], with parameters s(n), c(n) and ℓ(n) and q(n) as
follows: A language L is in this class iff there is a reduction taking an instance x
to a system of constraints (x) such that, for n = |x|,
—|(x)| ≤ℓ(n); and each constraint ϕ ∈(x) accesses at most q(n) variables.
—If x ∈L, then 1 −UNSAT((x)) ≥c(n)
—If x ̸∈L, then 1 −UNSAT((x)) ≤s(n)
Deﬁnition 8.2 (Locally Testable Codes).
A code C ⊂n is (q, δ, ε)-locally
testable if there is a randomized algorithm A that is given oracle access to a string
x, then (nonadaptively) reads at most q symbols from x, and decides whether to
accept or reject such that
—For every x ∈C, Pr[Ax accepts] = 1.
—For every string y ∈n such that rdist(y, C) ≥δ, Pr[Ay rejects] ≥ε.
8.2. SHORT PCPS.
Our main theorem in this section is,
THEOREM 8.3.
SAT ∈PCP 1
2 ,1[log2(n · poly log n), O(1)].
We prove this theorem by relying on a recent result of Ben-Sasson and Sudan,
THEOREM 8.4 ([BEN-SASSON AND SUDAN 2004, THEOREM 2.2]).
For
any
proper complexity function t : N →N,
NTIME(t(n)) ⊆PCP 1
2 ,1[log(t(n)poly log t(n)), poly log t(n)].
From this result, we derive SAT ∈PCP1−
1
poly log n ,1[log2(n · poly log n), O(1)].
More precisely,
LEMMA 8.5.
There exist constants c1, c2 > 0 and a polynomial-time re-
duction that transforms any SAT instance ϕ of size n into a constraint graph
G = ⟨(V, E), , C⟩such that
—size(G) ≤n(log n)c1 and || = O(1).
—If ϕ is satisﬁable, then UNSAT(G) = 0.
—If ϕ is not satisﬁable, then UNSAT(G) ≥
1
(log n)c2 .
Before proving the lemma, let us see how it implies Theorem 8.3,
PROOF OF THEOREM 8.3. Given a SAT instance of size n, we rely on Lemma 8.5
to reduce it to a constraint graph G whose size we denote by m = n · (log n)c1.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
31
Then, we apply the main theorem (Theorem 1.7) iteratively k = c2 · log log m <
2c2 log log n times. This results in a constraint-graph G′ for which UNSAT(G′) ≥
min(2k · UNSAT(G) , α) = α, and such that size(G′) = Cc2 log log m · m ≤n ·
(log n)c1+2c2 log C = n · poly log n.
To get an error-probability of 1
2, one can apply the expander-neighborhood sam-
pler of Goldreich and Wigderson [1997] (see also Goldreich [1997, Section C.4])
for efﬁcient ampliﬁcation.
PROOF OF LEMMA 8.5. Since SAT ∈NTIME(O(n)), Theorem 8.4 yields some
constants a1, a2 > 0 and a reduction from SAT to a system 0 of at most m =
n · (log n)a1 constraints, each over at most (log n)a2 Boolean variables such that
satisﬁable inputs go to satisﬁable systems, and unsatisﬁable inputs result in systems
for which any assignment satisﬁes at most 1
2 of the constraints. Our goal is to reduce
the number of queries per constraint. Basically, this is done by introducing new
variables over a large alphabet, which enables few queries in a naive way (which
causes the rejection probability to deteriorate). Then, the alphabet size is reduced
through composition.
Two-variable Constraints.
For each constraint in 0, let us introduce one new
(big) variable. This variable will take values over alphabet  = {0, 1}(log n)a2 that
supposedly represent values to all of the original (small) variables queried in that
constraint. The number of big variables is m = n ·(log n)a1. Introduce (log n)a2 new
constraints per big variable: Each constraint will query the big variable and exactly
one of the small variables queried by the corresponding constraint. The constraint
will check that the value for the big variable satisﬁes the original constraint, and
that it is consistent with the second (small) variable. Call this system  and observe
that || = n · (log n)a1+a2.
What is UNSAT()? Given an assignment for the original variables it must cause
at least m/2 (original) constraints to reject. Each big variable that corresponds to
a rejecting constraint must now participate in at least one new rejecting constraint.
Indeed, even if it is assigned a value that is accepting, it must differ from this
assignment, so it will be inconsistent with at least one original (small) variable.
Altogether, at least
m/2
m·(log n)a2 ≥(log n)−(a2+1) fraction of the constraints in  must
reject.
Composition.
We next apply composition to reduce the alphabet size from
log || = poly log n to O(1). This is exactly as done in Lemma 1.10 except that we
are somewhat more restricted in our choice of the assignment tester algorithm P (or
equivalently: a PCP of Proximity), in that the output size of P must be polynomial
in the input size.
Observe that we only require that the size of the output is
polynomial (and not quasilinear) in the input size, so there is no circularity in our
argument. Existence of such an algorithm P is an implicit consequence of the proof
of the PCP Theorem of Arora and Safra [1998] and Arora et al. [1998], and was
explicitly described in Ben-Sasson et al. [2004] and Dinur and Reingold [2004].
Here is a brief summary of the construction of Lemma 1.10: We encode each
variable via a linear dimension, linear distance error-correcting-code, treating the
‘small’ variable in each constraint as if its value lies in the large alphabet. We then
run P on each constraint and let the new system ′ be the union of the output
constraint systems.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
32
IRIT DINUR
Assuming that the rejection probability of P is ε = (1), the soundness analysis
shows that
UNSAT(′) ≥UNSAT() · ε = ((log n)−(a2+1)) =
1
poly log n
where the middle equality holds since ε is a constant. Since the input size for
P was the size of one constraint in , that is, poly log n, it follows that the
size of the constraint system output by P is also poly log n. This means that
′ = || · poly log n = n · poly log n.
8.3. SHORT LOCALLY TESTABLE CODES.
A similar construction to that of The-
orem 8.3 can be used to obtain locally-testable codes with inverse poly-logarithmic
rate (i.e., mapping k bits to k · poly log k bits), that are testable with a constant
number of queries.
The way we go about it is by relying on a variant of the main theorem (Theo-
rem 1.7). Recall that the main theorem is a reduction from G to G′ = (prep(G)t)◦P.
We will need a stronger kind of reduction, that is an assignment tester (also called
a PCP of Proximity), as deﬁned in Deﬁnition 2.8.
In the next section, we will prove that the main ampliﬁcation step (as in Theo-
rem 1.7) can also work for assignment-testers. Formally,
THEOREM 9.1.
There exists t
∈N such that given an assignment-tester
with constant-size alphabet  and rejection probability ϵ, one can construct
an assignment-tester with the same alphabet and rejection probability at least
min(2ϵ, 1/t), such that the output size of the new reduction is bounded by at most
a constant factor times the output size of the given reduction.
Just as our main theorem (Theorem 1.7) could be combined with the construction
of Ben-Sasson and Sudan [2004] yielding a short PCP, Theorem 9.1 can be com-
bined with the construction of Ben-Sasson and Sudan [2004] to yield short PCPs
of Proximity/assignment-tester reductions.
COROLLARY 8.6.
There exists an assignment-tester with constant size alpha-
bet, and constant rejection probability ϵ > 0, such that inputs of size n are trans-
formed to outputs of size at most n · poly log n.
PROOF.
As in the proof of Theorem 8.3, we begin with a lemma that follows
from the construction of Ben-Sasson and Sudan [2004],
LEMMA 8.7.
There exist a polynomial-time assignment-tester with constant
alphabet size and rejection probability ϵ ≥
1
(log n)O(1) , such that inputs of size n are
transformed to outputs of size at most n · poly log n.
The difference between this lemma and Lemma 8.5 is that here we require the
reduction to be an assignment-tester. This can be derived from the construction of
Ben-Sasson and Sudan [2004], in a similar way to the proof of Lemma 8.5.
Let A0 be the assignment-tester from Lemma 8.7. Let Ai be the result of applying
the transformation guaranteed in Theorem 9.1 on Ai−1. For i = O(log log n), the
reduction Ai will have the required parameters.
Finally, we claim that Corollary 8.6 directly implies the existence of locally
testable codes of rate 1/poly log n.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
33
COROLLARY 8.8.
For every δ > 0, there exists an ε = (δ) > 0, and an
inﬁnite family of codes {CN}N with rate 1/poly log N, such that CN is (2, δ, ε)-
locally-testable.
PROOF.
Assuming we have the assignment tester from Corollary 8.6, we apply
the construction of Ben-Sasson et al. [2004, Construction 4.3]. We give a brief
sketch of the construction. We construct CN as follows. Fix n ∈N and let C′
n ⊂n
be an error correcting code with rate and distance 
(n). Let  be a circuit over
variables X = {x1, . . . , xn} that accepts iff the assignment for X is a codeword
in C′
n. We can assume that || = O(n) (using, e.g., expander codes [Sipser and
Spielman 1996]). Run the reduction of Corollary 8.6 on , and let G be the output
constraint graph, size(G) = n · poly log n. Let Y = V \ X be the new variables
added by the reduction, and denote m = |Y|, m ≤n · poly log n. Let ℓ= 2m
δn ,
N = nℓ+ m, and deﬁne a new code
CN = {aℓb ∈nℓ+m | a ∈C′
n, b ∈m and UNSATσ(G) = 0
where σ|X = a and σ|Y = b} ⊂N,
where aℓb denotes the concatenation of ℓcopies of a with b. Clearly, the rate of CN
is 1/poly log N. We claim that CN is (2, δ, ε)-locally-testable. Here is the testing
algorithm for a given word w ∈nℓ+m. Denote the i-th bit of w by wi.
(1) Flip a random coin.
(2) If heads, choose a random i ∈[n] and a random j ∈{1, 2, . . . , ℓ−1}, and
accept iff wi = wi+ j·ℓ
(3) If tails, choose a random constraint in G. View w[1, . . . , n] as an assignment
for X and w[nℓ+ 1, . . . , nℓ+ m] as an assignment for Y. Accept iff the
constraint is satisﬁed by this assignment.
Clearly, every w ∈CN passes the test with probability 1. If rdist(w′, CN) > δ,
then for any codeword σ = aℓb ∈CN, since m ≤nℓ· δ
2, the strings w′ and σ must
differ on δnℓ/2 of their ﬁrst nℓbits. The reader may verify that the test rejects with
probability at least (δ).
Remark 8.9 (Constant Relative Distance). The codes above also have a constant
relative distance. This follows almost immediately from the distance of C′
n, except
for the following caveat. A problem would arise if for some assignment a for X that
satisﬁes  there are two assignments b1, b2 for Y such that both UNSATa∪b1(G) = 0
and UNSATa∪b2(G) = 0. This would imply that aℓb1, aℓb2 ∈CN, and their distance
can be quite small. However, this can be ruled out if every assignment a has only one
assignment b such that UNSATa∪b(G) = 0. This can be ensured here, and therefore
we conclude that the above does yield codes with constant relative distance.
9. Adapting the Main Theorem for Assignment-Testers
In this section, we show how to adapt the main ampliﬁcation step (Theorem 1.7),
that was described as a reduction between constraint graphs, to work within the
more demanding framework of an assignment-tester. This gives an extension of our
main theorem (and Theorem 1.3), to assignment-testers / PCPs of proximity.
THEOREM 9.1.
There exists t
∈N and |0| > 1 such that given an
assignment-tester with constant-size alphabet  and rejection probability ϵ, one
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
34
IRIT DINUR
can construct an assignment-tester with alphabet 0 and rejection probability at
least min(2ϵ, 1/t), such that the output size of the new reduction is bounded by at
most C times the output size of the given reduction, and C depends only on ||.
Suppose we have a reduction taking  to G. We construct from G a new graph G′
and prove that the reduction taking  to G and then to G′ has the desired properties.
Let H = (prep(G))t be the result of running the preprocessing step (Lemma 1.9)
and then raising the resulting constraint graph to the power t. What are the variables
of H? Going from G to prep(G) each variable v ∈V is split into many copies,
and we denote the set of copies of v by [v]. Next, going from prep(G) to H =
(prep(G))t, the variables of H are identical to those of prep(G), but take values from
a larger alphabet. So denoting the variables of H by VH, we have VH = ∪v∈V [v].
Syntactically, VH is disjoint from V , although the values for VH are supposed to
“encode” values for V . Indeed, an assignment σ : V → can be mapped to an
assignment σ2 : VH →dt/2 that “encodes” it, by the following two steps.
(1) First deﬁne a mapping σ $→σ1, where the assignment σ1 : VH → for
prep(G) is deﬁned by assigning all copies of v the same value as σ(v):
∀v ∈V w ∈[v],
σ1(w)
△= σ(v).
(13)
Let us name this mapping m1. Observe also that given any assignment for
prep(G), σ ′ : VH →, it can be “decoded” into an assignment for G according
to “popularity” as follows. Simply set σ = m−1
1 (σ ′) to be an assignment σ :
V → for which m1(σ) is closest5 in Hamming distance to σ ′.
(2) Next, deﬁne a mapping σ1 $→σ2, where the assignment σ2 : VH →dt/2 for
H is deﬁned by assigning each vertex w a vector consisting of the σ1-values of
all vertices reachable from w by a t/2-step walk
∀w ∈VH, σ2(w)v
△= σ1(v) for all v reachable from w by a t/2-step walk in G .
(14)
Let us name this mapping m2, and again, given any assignment σ ′ : VH →dt/2
for (prep(G))t it can be “decoded” into an assignment for prep(G) as follows.
Simply set σ = m−1
2 (σ ′) to be the assignment deﬁned by
σ(v)
△= max arga∈{Pr[A random ⌈t/2⌉-step walk from v reaches a vertex w
for which σ ′(w)v = a]} .
This coincides with the “most popular opinion” assignment as deﬁned in Eq.
(4) of Section 6.
Going back to our reduction, we recall that in order for our reduction to be
an assignment-tester, our output constraint graph must have the variables X of 
contained in its set of variables. Then, we must also verify that the completeness
and soundness conditions (that refer to X) hold.
5Breaking ties arbitrarily.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
35
The Graph H ′.
We next transform H to H ′ so as to include X among the
variables of H ′. The vertices of H ′ will be VH ∪X. The constraints of H ′ will
include all of the constraints of H, and also additional constraints that will check
that the assignment for VH is a correct encoding, according to the mapping m2 ◦m1
which maps σ to σ2 (via σ1), of the assignment for X.
We describe the constraints between X and VH by the following randomized
procedure. Let A : VH →dt/2 and let a : X →{0, 1}.
(1) Select x ∈R X.
(2) Select z ∈R [x] (recall that [x] is the set of vertices in prep(G) that are copies
of x).
(3) Take a t/2-step random walk in prep(G) starting from z, and let w be the
endpoint of the walk. Accept if and only if A(w)z = a(x).
For every possible random choice of the test, we will place (an edge and) a
constraint between w and x, that accepts iff the test accepts. We will reweigh the
constraints (by duplication) so that the weight of the comparison constraints deﬁned
by the random procedure is half of the total weight of the edges. This completes
the description of H ′. Observe that the size of H ′ is at most a constant times the
size of G, because prep(G) is d-regular for d = O(1), so every vertex w ∈VH
participates in exactly dt/2 = O(1) new comparison constraints. The next lemma
states that the reduction from  to H ′ is an assignment-tester with large alphabet,
and rejection probability 
(√t) · ϵ.
LEMMA 9.2.
Assume ε < 1/t, and ﬁx a : X →{0, 1}.
—If a ∈SAT(), there exists b : VH →dt/2 such that UNSATa∪b(H ′) = 0.
—If δ = rdist(a, SAT()) > 0, then for every b : VH →dt/2, UNSATa∪b(H ′) >
δ · min( 1
16, (β1β2
√t/2)ε).
We prove this lemma shortly below. First, note that the constraint graph H ′ is
almost what we need, except that it is deﬁned over the alphabet dt/2, rather than
over . Let us now proceed to construct the ﬁnal graph G′.
The Graph G′.
To reduce the alphabet of H ′, we use composition. That is, we
assume that we have at our disposal an assignment-tester P such that its rejection
probability is some constant ε0 > 0, and its alphabet is 0. We make no require-
ments about the length of the output of P, because we will only run it on inputs of
bounded size. For example, we can use the construction given in Section 7.
Now, the Composition Theorem of assignment-testers, [Dinur and Reingold
2004, Theorem 3.7], states that given any two such reductions, their composi-
tion is well deﬁned (it is essentially described in the proof of Lemma 1.10 herein)
and is itself an assignment-tester, with the following parameters:
—The alphabet size is that of the inner reduction P, thus the constraints in G′ are
over alphabet 0, as desired.
—The output size is the product of the output sizes of the two reductions. In our
case, this means that the output size of the reduction  ⇒H ′ is multiplied by
a constant factor that is the maximum size of the output of P when run on a
constraint of H ′.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
36
IRIT DINUR
—The rejection probability is the product of the rejection probabilities of the
two reductions. Thus, denoting the rejection probability of P by ε0, it is ε0
times the rejection probability of the reduction  ⇒H ′. Since this value was
min( 1
16, (β1β2
√t/2)ε), by choosing t large enough, even after multiplying by ε0
it is still larger than 2ε for all small enough ε.
This completes the description of the transformation taking  to G′. It remains
to prove Lemma 9.2.
PROOF OF LEMMA 9.2. In this proof, there are four constraint graphs that we
keep in mind
G
⇒
prep(G)
⇒
H = (prep(G))t
⇒
H ′ .
Recall that we encode assignments for G via m1, obtaining assignments for prep(G).
These are encoded via m2, giving assignments for H. We can also go in the opposite
direction where an assignment for H can be decoded into an assignment for prep(G)
via m−1
2 , and similarly an assignment for prep(G) can be decoded via m−1
1
into as
assignment for G.
—Suppose a ∈SAT(). Then, by assumption on the reduction from  to G,
there is an assignment b : V → such that σ = a ∪b satisﬁes all constraints
in G. The assignment σ is mapped, via m1 to an assignment σ1 for prep(G),
and σ1 in turn is mapped via m2 into an assignment for H: σ2 : VH →dt/2.
By the completeness of the preprocessing and the powering, σ2 will satisfy all
constraints in H. It is easy to verify that σ2 will also satisfy (together with a) all
of the new comparison constraints, so UNSATa∪σ2(H ′) = 0
—Assume now rdist(a, SAT()) = δ > 0. Fix some assignment b : VH →dt/2.
We will show that the assignment a∪b violates many of the constraints. The idea
is to ﬁrst “decode” b (through m−1
2
and then m−1
1 ) thereby getting an assignment
b0 : V →. Then, we show that either b0 is close to the assignment a, in which
case it is far from SAT(), so by ampliﬁcation b must violate many of the
constraints in H. Otherwise, if b0 is far from a, then many (a constant fraction!)
of the comparison constraints will fail. So let b1 = m−1
2 (b) be an assignment for
the vertices of prep(G), and let b0 = m−1
1 (b1) be an assignment for the vertices of
G, where notation m−1
1 , m−1
2 was deﬁned in steps (1) and (2) of the construction.
There are two cases.
—If rdist(b0|X, a) ≤δ/2 then rdist(b0|X, SAT()) ≥δ/2 by the triangle in-
equality.Sincethereductionfromto G isanassignment-testerwithrejection
probability ε, this means that no matter what b0|(V \X) is, UNSATb0(G) ≥εδ/2.
Nowweclaimthatb1 mustalsobeviolatingasimilarfractionoftheconstraints
of prep(G):
UNSATb1(prep(G)) ≥εδ/2 · β1.
(15)
Indeed, recall Corollary 4.5 that asserts that for every G and for every assign-
ment σ ′ for prep(G), the fraction of constraints of prep(G) violated by σ ′ is
proportional to the fraction of constraints of G violated by m−1
1 (σ ′). Plugging
in b1 for σ ′, and since b0 = m−1
1 (b1), this implies (15).
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
37
Next, we claim that b must be violating an even larger fraction of H =
(prep(G))t than UNSATb1(prep(G)):
UNSATb((prep(G))t) ≥β2
√
t · min
1
t , UNSATb1(prep(G))

.
(16)
Indeed, this follows precisely from Lemma 6.1 that states that for every G
and every assignment ⃗σ for Gt, the fraction of constraints of Gt violated
by ⃗σ is larger than the fraction of constraints of G violated by the “popular
opinion” assignment, by factor (√t). Observe that indeed m−1
2 (⃗σ) is the
“popular opinion” assignment. Plugging in b for ⃗σ, and since b1 = m−1
2 (b),
this implies (16). Combining (15) and (16), and observing that by assumption
1/t is clearly larger than ε > UNSATb1(prep(G)),
UNSATb(H) ≥εδ/2 · β1 · β2
√
t .
Since the constraints of H are half of the constraints of H ′, we have
UNSATa∪b(H ′) ≥1
2
UNSATb(H) ≥εδ/4 · β1 · β2
√
t.
—If rdist(b0|X, a) > δ/2, then we will show that δ/8 fraction of the comparison
constraints reject. Indeed, with probability at least δ/2 the randomized test
selects, in Step (1), a variable x ∈X for which b0(x) ̸= a(x). Conditioned
on that, consider the probability that in step (2) a variable z ∈[x] is selected
such that b1(z) ̸= a(x). Since b0(x) is, by deﬁnition, a most popular value
among values assigned by b1 to the copies of x, and since by conditioning
a(x) ̸= b0(x), this probability is at least 1/2. Conditioned on both previous
events occurring, Step (3) selects a vertex w for which b(w)z ̸= a(x), with
probability at least 1/2 (for similar reasoning). Altogether, with probability
at least δ
2 · 1
2 · 1
2 = δ/8 the test rejects. This means that at least δ/16 of the
total number of tests reject, that is, UNSATa∪b(H ′) ≥δ/16.
We have proven that for δ = rdist(a, SAT()), and for every assignment b, the
rejection probability UNSATa∪b(H ′) is either at least δ· 1
16 or at least δ·(β1β2
√t/2·
ε).
This completes the proof.
Theorem 9.1 also gives an immediate combinatorial construction of assignment-
testers or PCPPs in the same way that the main theorem (Theorem 1.7) was used
to derive the PCP Theorem (Theorem 1.3).
COROLLARY 9.3.
There is an assignment-tester, with constant alphabet, con-
stant rejection probability, and polynomial output length.
PROOF.
Given a circuit  it is easy to construct a constraint graph G0 such that
the reduction  $→G0 is an assignment-tester with rejection probability 1/ |G0|.
Letusnamethis(trivial)assignmenttesterP0.Letusdenotetherejectionprobability
of an assignment tester P by ε(P). We can now construct Pi inductively for every
i ≥1. Indeed, for every i ≥0, let us construct Pi+1 by applying the transformation
guaranteed in Theorem 9.1 to Pi. The theorem asserts that the assignment-tester
Pi+1 maps  to Gi+1 such that
(1) The alphabet of Gi+1 is 0.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
38
IRIT DINUR
(2) ε(Pi+1) ≥min( 1
t , 2ε(Pi)), where t is a global constant.
(3) The running time of Pi+1 is at most a constant C times the running time of Pi.
We now prove that for k = log2 n, where n = size(G0), Pk is the desired
assignment tester. Clearly the alphabet is 0. It is also easy to see by induction that
the running time of Pk is at most Ck = poly(n) times the running time of P0. Since
P0 runs in polynomial-time, altogether Pk is a polynomial-time transformation.
It remains to show that ε(Pk) ≥1/t. Indeed, if for some i∗< k, ε(Pk) ≥1/t
then for every i > i∗ε(Pi) ≥1/t and in particular this holds for Pk. Otherwise, it
follows by induction from item 2 above that ε(Pk) ≥2kε(P0) > 1/t.
10. Graph Powering and Parallel-Repetition
The celebrated parallel repetition theorem of Raz [1998] gives a different method
of ampliﬁcation. Given a system C of constraints, a new system Cℓ
 is constructed
by taking new variables corresponding to ℓ-tuples of the old variables, and new
constraints corresponding to ℓ-tuples of the old constraints (we ignore the issue of
bipartiteness in this discussion). The alphabet grows from  to ℓ. The theorem
asserts that given a system of constraints C with UNSAT(C) = α, the ℓ-parallel-
repetition system, Cℓ
, will have UNSAT(Cℓ
) ≥1 −(1 −α)
(ℓ).
Our graph powering construction can be viewed as setting ℓ= dt/2 (where the
graph underlying the constraints is d-regular) and taking a small and carefully
chosen subset of the ℓ-tuples of variables and of the ℓ-tuples of constraints. Viewed
this way, the graph powering construction is a ‘derandomization’ of the parallel-
repetition theorem. We recall that Feige and Kilian [1995] proved that no generic
derandomization of the parallel-repetition theorem is possible. Their result focuses
on a range of parameters that does not apply to our setting. This raises questions
about the limits of such constructions in a wider range of parameters.
Let us conclude by mentioning a speciﬁc setting of the parameters which is of par-
ticular interest. When the unsat value of a constraint system is some ﬁxed constant,
then applying the parallel repetition transformation results in a new system whose
unsat value approaches 1 as ℓincreases. This feature is very useful in inapproxima-
bilityreductions.Ontheotherhand,ourampliﬁcationstopstomakeanyprogressfor
constant α > 0, as is demonstrated in the instructive example of Bogdanov [2005].
Of course, the main advantage of our ‘derandomized’ construction is that the
new system size is only linear in the old system size. This feature is essential for
our inductive proof of the PCP theorem.
Appendixes
A. A Lemma about Similar Binomial Distributions
For n ∈N and p ∈(0, 1), let Bn,p denote a binomially distributed random variable,
that is, Pr[Bn,p = k] =
n
k

pk(1 −p)n−k. The following lemma asserts that if n, m
are close, then the distributions of Bn,p and Bm,p are close.
LEMMA 6.5. For every p ∈(0, 1) and c > 0, there exists some 0 < τ < 1 and
n0 such that, if n0 < n −√n ≤m < n + √n, then
∀k ∈N, |k −pn| ≤c√n,
τ ≤Pr[Bn,p = k]
Pr[Bm,p = k] ≤1
τ .
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
39
PROOF.
Assume ﬁrst that m ≤n. We write n = m + r for some 0 ≤r ≤√n
and use the identity
m+1
k

=
m+1
m+1−k
m
k

,
Pr[Bn,p = k] =
m + r
k

pk(1 −p)m+r−k
=
m + 1
m + 1 −k ·
m + 2
m + 2 −k · · ·
m + r
m + r −k
m
k

·pk(1 −p)m−k(1 −p)r
= X · pk(1 −p)m−k
m
k

= X · Pr[Bm,p = k]
where X = (1 −p)r
m+1
m+1−k ·
m+2
m+2−k · · ·
m+r
m+r−k is bounded as follows. Let Xa =
m+a
m+a−k . For all a ≤r ≤√n we have Xa =
1
1−(k/(m+a)) and clearly
1
1 −(k/m) ≥
1
1 −(k/(m + a)) ≥
1
1 −(k/n).
Wewillchoosen0 largeenoughtomakealloftheexpressionsbelowstrictlypositive.
Since k ≥pn −c√n,
Xa ≥
1
1 −(k/n) ≥
1
1 −p + (c/√n) =
1
1 −p ·
1
1 + (c/(1 −p))(1/√n).
Now, X = (1 −p)r · r
a=1 Xa ≥(1 +
c
1−p
1
√n)−r =: τ1.
Similarly, since n −√n < m and pn −c√n ≤k it follows that 1 −(k/m) ≥
1 −p −((c + 1)/√n). So
Xa ≤
1
1 −(k/m) ≤
1
1 −p −((c + 1)/√n) =
1
1 −p·
1
1 −((c + 1)/(1 −p)(√n)),
and we have X = (1 −p)r · r
a=1 Xa ≤(1 −
c+1
(1−p)(√n−1))−r =: τ2. Clearly, since
r ≤√n both τ1 and τ2 can be bounded by constants (independent of n), and we
take τ = min(τ1, τ −1
2 ).
Finally, if n < m, then since clearly m −√m < n < m we can deduce the result
from applying the lemma with the roles of m and n reversed, the same p, and the
constant c′ = c + 1.
B. The Long Code Test
In this section, we prove Theorem 7.1. Let us identify {0, 1}s with [n] (where
n = 2s) in an arbitrary way. We consider Boolean functions ψ : [n] →{1, −1} by
identifying −1 with true (so a ∈[n] is said to satisfy ψ iff ψ(a) = −1). Recall
that L = { f : [n] →{−1, 1}} is the set of Boolean functions on [n]. We restate
Theorem 7.1 with this modiﬁed notation.
THEOREM 7.1. There exists a Long-Code Test T that is a randomized algorithm
that has input a function ψ : [n] →{1, −1}, and also oracle access to a folded
string A : L →{1, −1}. T reads the input ψ and tosses some random coins.
Based on these it computes a three-bit predicate w : {0, 1}3 →{true, false} and
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
40
IRIT DINUR
three locations f1, f2, f3 ∈L in which it queries the string A. It then outputs
w(A( f1), A( f2), A( f3)). Denote an execution of T with access to input ψ and
folded string A by T A(ψ). Then the following hold,
—Perfect completeness: If a ∈[n] such that ψ(a) = −1, then Pr[T Aa(ψ) = true] =
1.
—Strong6 soundness: For every δ ∈[0, 1], if A : L →{1, −1} is folded and at least
δ-far from Aa for all a for which ψ(a) = −1, then Pr[T A(ψ) = false] ≥(δ).
Our proof is basically a reworking of a test of H˚astad [2001], into our easier
setting:
Standard Deﬁnitions.
We identify L = { f : [n] →{−1, 1}} with the Boolean
hypercube {1, −1}n, and use letters f, g for points in the hypercube. We use letters
A, B or χ to denote functions whose domain is the hypercube7. For α ⊂[n], deﬁne
χα : {−1, 1}n →{−1, 1},
χα( f )
△=

i∈α
f (i) .
The characters {χα}α⊆[n] form an orthonormal basis for the space of func-
tions {A : {−1, 1}n →R}, where inner product is deﬁned by ⟨A, B⟩
=
E f [A( f )B( f )] = 2−n 
f A( f )B( f ). It follows that any function A : {−1, 1}n →
{−1, 1} can be written as A = 
α ˆAαχα, where ˆAα = ⟨A, χα⟩. We also have Par-
seval’s identity, 
α | ˆAα|2 = ⟨A, A⟩= 1.
The Test.
Let ψ : [n] →{−1, 1} be some predicate and ﬁx τ =
1
100. Let
A : {−1, 1}n →{−1, 1} be a folded string, that is, for all f ∈{−1, 1}n A(−f ) =
−A( f ) and also A( f ) = A( f ∧ψ) where f ∧ψ is deﬁned by
∀a ∈[n],
( f ∧ψ)(a) =
 −1 f (a) = −1 and ψ(a) = −1
1
otherwise.
.
A function A : {1, −1}n →{1, −1} is the legal encoding of the value a ∈[n] iff
A( f ) = f (a) for all f ∈L. The following procedure tests whether A is close to a
legal encoding of some value a ∈[n] that satisﬁes ψ.
(1) Select f, g ∈L uniformly at random.
(2) Set h = gμ where μ ∈L is selected by doing the following independently for
every y ∈[n]. If f (y) = 1 set μ(y) = −1. If f (y) = −1 set
μ(y) =
 1
with probability. 1 −τ
−1 with probability τ.
(3) Accept unless A(g) = A( f ) = A(h) = 1.
6 We refer to ‘strong’ soundness as opposed to regular soundness, since due to the stronger property
of having the rejection probability proportional to the distance from a “good” string.
7We consider here functions whose domain is an arbitrary set of size n, and wlog we take the set [n].
In the application this set is usually some {0, 1}s but we can safely ignore this structure, and forget
that n = 2s.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
41
It is clear that the test behaves according to the description in Theorem 7.1. It
remains to prove completeness and soundness.
PROPOSITION B.1 (COMPLETENESS).
If a ∈[n] such that ψ(a) = −1, then
Pr[T Aa(ψ) = true] = 1.
PROOF.
It is easy to check completeness: We ﬁx some a ∈[n] for which
ψ(a) = −1 and assign for all f , A( f ) = f (a). Clearly, A is folded. Also, if
A( f ) = f (a) = −1 then the test accepts. Finally, if A( f ) = f (a) = 1 then
A(h) = h(a) = −g(a) = −A(g) ̸= A(g), and again the test accepts.
PROPOSITION B.2 (SOUNDNESS).
There exists a constant c > 0 such that for
every δ ∈[0, 1], if A : L →{1, −1} is folded and at least δ-far from Aa for all a
for which ψ(a) = −1, then Pr[T A(ψ) = false] ≥c · δ.
PROOF.
Let us ﬁx δ ∈(0, 1] and assume that A is δ-far from every Aa for
a ∈[n] that satisﬁes ψ. Denote the rejection probability of the test by Pr[T A(ψ) =
false] = ε. The proof of soundness will be based on the following proposition.
PROPOSITION B.3.
There exists a constant C > 0 such that if T rejects with
probability ε then

|α|>1
| ˆAα|2 ≤Cε.
We defer the proof of the proposition to later. We will need the following result,
THEOREM B.4 ([FRIEDGUT ET AL. 2002]).
There is a global constant C′ > 0
(independent of n) such that the following holds. Let ρ > 0 and let A : {1, −1}n →
{1, −1} be a Boolean function for which 
α,|α|>1 | ˆAα|2 < ρ. Then either | ˆAφ|2 ≥
1 −C′ρ, or for some i ∈[n], | ˆA{i}|2 ≥1 −C′ρ.
It is well known that since A is folded ˆAα = 0 whenever (i) |α| is even, or (ii)
∃i ∈α for which ψ(i) = 1 (recall that 1 corresponds to false). The reason is that
we can partition {1, −1}n into pairs f, f ′ such that
ˆAα = 2−n 
f
A( f )χα( f ) = 2−n · 1
2

f
(A( f )χα( f ) + A( f ′)χα( f ′)) = 2−n−1 
f
0 = 0 .
In (i), let f ′ = −f , so χα( f ) = χα( f ′) but A( f ) = −A( f ′). In (ii) let f ′ = f +ei
wherei is an index for which ψ(i) = 1; so χα( f ) = −χα( f ′) but A( f ) = A( f ′). We
can thus deduce from Theorem B.4 that there is some i ∈[n] for which ψ(i) = −1
and | ˆA{i}|2 ≥1 −C′Cε.
This means that one of the following holds,
(1) ˆA{i} ≥
√
1 −C′Cε ≥1 −C′Cε, or
(2) −ˆA{i} ≥√1 −C′Cε ≥1 −C′Cε.
Since by deﬁnition ˆAα = E f [A( f )χα( f )] = 1 −2rdist(A, χα), it follows that
rdist(A, χ{i}) = 1−ˆA{i}
2
. If the ﬁrst item holds, then clearly rdist(A, χ{i}) ≤CC′ε/2
and we are done by choosing c ≤2/CC′. Suppose the second item holds, we will
show that ε is larger than some absolute constant, and by choosing c smaller than
that constant we will be done. Imagine ﬁrst that −ˆA{i} = 1, that is, A = −χ{i}. Then,
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
42
IRIT DINUR
the probability (over the choice of f, g, and h) that f (i) = −1 and g(i) = −1 and
h(i) = −1 is at least 1
4 ·(1−τ), and in this case we have A( f ) = A(g) = A(h) = 1
and the test rejects (so ε ≥(1 −τ)/4 > 1/8). This probability can go down by at
most 3rdist(A, −χ{i}) (which is an upper bound on the probability that at least one
of f, g, h is a point of disagreement between A and −χ{i}). We get
ε ≥1 −τ
4
−3rdist(A, −χ{i}) > 1
8 −3CC′ε
rearranging we get ε >
1
8(1+3CC′).
Choosing
c = min
 2
CC′ ,
1
8(1 + 3CC′)

,
we have proven that A is δ-far from every χ{i} for a value of i that satisﬁes ψ, then
the test rejects with probability at least cδ.
It remains to prove the proposition.
PROOF OF PROPOSITION B.3. Let us arithmetize the acceptance probability as
follows:
1 −ε = Pr[Test accepts] = E f,g,h

1 −(1 + A( f ))(1 + A(g))(1 + A(h))
8

=
and note that since the pairs ( f, g) and ( f, h) are pairs of random independent
functions, and since E[A] = ˆAφ = 0 due to A being folded, this equals,
= 7
8 −1
8Eg,h [A(g)A(h)] −1
8E f,g,h [A( f )A(g)A(h)] .
Using the Fourier expansion A(g) = 
α ˆAαχα(g), the ﬁrst expectation can be
written as
Eg,h
 
α,β⊆[n]
ˆAα ˆAβχα(g)χβ(h)

=

α⊆[n]
ˆA2
α(−τ)|α|,
which is bounded by τ in absolute value, since ˆAφ = 0. Recall that the entire
expression is equal 1 −ε by assumption. This implies that the second expectation
(whose value let us name W) must be at most −1 + τ + 8ε. We write it as
−1 + τ + 8ε ≥W = Eg, f,μ


α,β,γ ⊆[n]
ˆAα ˆAβ ˆAγ χα(g)χβ(gμ)χγ ( f )

=
=

α,γ ⊆[n]
ˆAγ ˆA2
αE f,μ[χα(μ)χγ ( f )]
=

γ ⊆α⊆[n]
ˆAγ ˆA2
α(−1 + τ)|γ |(−τ)|α\γ |,
where the last equality holds because of the correlation of μ and f . In particular,
(i) if γ ̸⊆α then E f,μ[χα(μ)χγ ( f )] = 0, and (ii) for every i ∈[n], E[μ(i)] = τ
and E[ f (i)μ(i)] = −1 + τ.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
The PCP Theorem by Gap Ampliﬁcation
43
We now bound the absolute value of this sum, following H˚astad [2001]. First we
claim that

γ ⊆α
((1 −τ)|γ |(τ)|α\γ |)2 ≤(1 −τ)|α| .
The left-hand side is the probability that tossing 2 |α| independent τ-biased coins
results in a pattern γ γ where γ ∈{0, 1}|α|. This probability is (τ 2 + (1 −τ)2)|α| ≤
(1 −τ)|α| since τ < 1 −τ. By the Cauchy–Schwarz inequality,

γ ⊆α
| ˆAγ |(1 −τ)|γ |(τ)|α\γ | ≤

γ ⊆α
| ˆAγ |2 ·

γ ⊆α
((1 −τ)|γ |(τ)|α\γ |)2 ≤(1 −τ)|α|/2
so, splitting the sum into |α| = 1 and |α| > 1,
|W| ≤

|α|=1
| ˆA2
α|(1 −τ) +

|α|>1
| ˆAα|2(1 −τ)|α|/2 .
Let ρ = 
|α|>1 | ˆAα|2. We have |W| ≤(1 −ρ)(1 −τ) + ρ(1 −τ)3/2, since ˆAα = 0
for |α| even. Thus
1−τ−8ε ≤|W| ≤(1−τ)((1−ρ)+ρ
√
1 −τ)
⇒
ρ ≤
8ε
(1 −τ)(1 −
√
1 −τ)
.
Since τ =
1
100 is ﬁxed, we have ρ = O(ε).
ACKNOWLEDGMENTS.
I am thankful to Omer Reingold and Luca Trevisan for many
discussions, especially ones about combinatorial analyses of graph powering, which
were the direct trigger for the ampliﬁcation lemma. I would like to thank Jaikumar
Radhakrishnan for very helpful comments on an earlier version of this manuscript,
andtheanonymousrefereeswhoseexcellentcommentsgreatlyimprovedthequality
of the manuscript. I would also like to thank David Arnon, Miki Ben-Or, Ehud
Friedgut, Oded Goldreich, and Alex Samorodnitsky for helpful comments.
REFERENCES
ARORA, S. 1994.
Probabilistic checking of proofs and the hardness of approximation problems. Ph.D.
dissertation, U.C. Berkeley. (Available via anonymous ftp as Princeton TR94-476.)
ARORA, S., LUND, C., MOTWANI, R., SUDAN, M., AND SZEGEDY, M. 1998.
Proof veriﬁcation and in-
tractability of approximation problems. J. ACM 45, 3, 501–555.
ARORA, S., AND SAFRA, S. 1998.
Probabilistic checking of proofs: A new characterization of NP. J.
ACM 45, 1, 70–122.
BABAI, L. 1985.
Trading group theory for randomness. In Proceedings of the 17th ACM Symposium on
Theory of Computing. ACM, New York, 421–429.
BABAI, L., FORTNOW, L., AND LUND, C. 1991.
Non-deterministic exponential time has two-prover in-
teractive protocols. Computat. Complex. 1, 3–40.
BEN-OR, M., GOLDWASSER, S., KILIAN, J., AND WIGDERSON, A. 1988.
Multi prover interactive proofs:
How to remove intractability assumptions. In Proceedings of the 20th ACM Symposium on Theory of
Computing. ACM, New York, 113–131.
BEN-SASSON, E., GOLDREICH, O., HARSHA, P., SUDAN, M., AND VADHAN, S. 2004.
Robust PCPs of
proximity, shorter PCPs and applications to coding. In Proceedings of the 36th ACM Symposium on
Theory of Computing. ACM, New York.
BEN-SASSON, E., AND SUDAN, M. 2004.
Robust locally testable codes and products of codes. In RAN-
DOM: International Workshop on Randomization and Approximation Techniques in Computer Science.
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
44
IRIT DINUR
BEN-SASSON, E., SUDAN, M., VADHAN, S. P., AND WIGDERSON, A. 2003.
Randomness-efﬁcient low
degree tests and short PCPs via epsilon-biased sets. In Proceedings of the 35th ACM Symposium on
Theory of Computing. ACM, New York, 612–621.
BOGDANOV, A. 2005.
Gap ampliﬁcation fails below 1/2. Comment on ECCC TR05-046, can be found
at http://eccc.uni-trier.de/eccc-reports/2005/TR05-046/commt01.pdf.
DINUR, I., AND REINGOLD, O. 2004.
Assignment testers: Towards combinatorial proofs of the PCP
theorem. In Proceedings of the 45th Symposium on Foundations of Computer Science (FOCS). IEEE
Computer Society Press, Los Alamitos, CA.
FEIGE, U., GOLDWASSER, S., LOV´ASZ, L., SAFRA, S., AND SZEGEDY, M. 1996.
Approximating clique is
almost NP-complete. J. ACM 43, 2, 268–292.
FEIGE, U., AND KILIAN, J. 1995.
Impossibility results for recycling random bits in two-prover proof
systems. In Proceedings of the 27th ACM Symposium on Theory of Computing. 457–468.
FORTNOW, L., ROMPEL, J., AND SIPSER, M. 1994.
On the power of multi-prover interactive protocols.
Theoret. Comput. Sci. 134, 2, 545–557.
FRIEDGUT, E., KALAI, G., AND NAOR, A. 2002.
Boolean functions whose Fourier transform is concen-
trated on the ﬁrst two levels. Adv. Appl. Math. 29, 427–437.
GOLDREICH, O. 1997.
A sample of samplers a computational perspective on sampling. Electronic Col-
loquium on Computational Complexity TR97-020.
GOLDREICH,O., ANDSAFRA,S. 1997.
Acombinatorialconsistencylemmawithapplicationtoprovingthe
PCP theorem. In RANDOM: International Workshop on Randomization and Approximation Techniques
in Computer Science. Lecture Notes in Computer Science, Springer-Verlag, New York.
GOLDREICH, O., AND SUDAN, M. 2002.
Locally testable codes and PCPs of almost-linear length. In
Proceedings of the 43rd IEEE Symposium on Foundations of Computer Science. IEEE Computer Society
Press, Los Alamitos, CA, 13–22.
GOLDREICH, O., AND WIGDERSON, A. 1997.
Tiny families of functions with random properties: A quality
size trade off for hashing. J. Random Struct. Algorithms 11, 4, 315–343.
GOLDWASSER, S., MICALI, S., AND RACKOFF, C. 1989.
The knowledge complexity of interactive proofs.
SIAM J. Comput. 18, 186–208.
HARSHA, P., AND SUDAN, M. 2001.
Small PCPs with low query complexity. In Proceedings of the 18th
Annual Symposium of Theoretical Aspects of Computer Science. Lecture Notes in Computer Science,
vol. 2010. Springer-Verlag, New York, 327–338.
H˚ASTAD, J. 2001.
Some optimal inapproximability results. J. ACM 48, 798–859.
LINIAL, N., AND WIGDERSON, A. 2003.
Expander graphs and their applications. Lecture notes of a course:
http://www.math.ias.edu/ boaz/ExpanderCourse/.
LUND, C., FORTNOW, L., KARLOFF, H., AND NISAN, N. 1992.
Algebraic methods for interactive proof
systems. J. ACM 39, 4 (Oct.), 859–868.
O’DONNELL, R., AND GURUSWAMI, V. 2005.
Lecture notes from a course on the PCP theorem and
hardness of approximation.
PAPADIMITRIOU, C., AND YANNAKAKIS, M. 1991.
Optimization, approximation and complexity classes.
J. Comput. Syst. Sci. 43, 425–440.
POLISHCHUK, A., AND SPIELMAN, D. 1994.
Nearly linear size holographic proofs. In Proceedings of the
26th ACM Symposium on Theory of Computing. ACM, New York, 194–203.
RADHAKRISHNAN, J. 2006.
Gap ampliﬁcation in PCPs using lazy random walks. In Proceedings of the
33rd International Colloqium on Automata, Languages, and Programming (Venice, Italy, July 10–14).
Lecture Notes in Computer Science, vol. 4051. Springer-Verlag, New Yrok.
RAZ, R. 1998.
A parallel repetition theorem. SIAM J. Comput. 27, 3 (June), 763–803.
REINGOLD,O. 2005.
Undirectedst-connectivityinlog-space.InProceedingsofthe37thACMSymposium
on Theory of Computing.
REINGOLD, O., VADHAN, S., AND WIGDERSON, A. 2002.
Entropy waves, the zig-zag graph product, and
new constant-degree expanders and extractors. Ann. Math. 155, 1, 157–187.
SHAMIR, A. 1992.
IP = PSPACE. J. ACM 39, 4 (Oct.), 869–877. (Preliminary version in 1990 FOCS,
pp. 11–15.)
SIPSER, M., AND SPIELMAN, D. A. 1996.
Expander codes. IEEE Trans. Inform. Theory 42, 6, part 1,
Codes and complexity, 1710–1722.
RECEIVED DECEMBER 2005; REVISED FEBRUARY 2007; ACCEPTED FEBRUARY 2007
Journal of the ACM, Vol. 54, No. 3, Article 12, Publication date: June 2007.
