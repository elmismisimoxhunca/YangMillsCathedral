Title: Download

URL Source: https://projecteuclid.org/download/pdf_1/euclid.cmp/1103899050

Number of Pages: 26

Markdown Content:
Commun. math. Phys. 42, 281—305 (1975) © by Springer-Verlag 1975 

# Axioms for Euclidean Green's Functions II 

Konrad Osterwalder* 

Jefferson Laboratory of Physics, Harvard University, Cambridge, Massachusetts, USA 

Robert Schrader 

Institut fur Theoretische Physik, Freie Universitat Berlin, Berlin with an Appendix by Stephen Summers Received December 3, 1974; in revised form January 16, 1975 

Abstract. We give new (necessary and) sufficient conditions for Euclidean Green's functions to have analytic continuations to a relativistic field theory. These results extend and correct a previous paper. 

Table of Contents 

I. Introduction 281 II. Notations 283 III. The Equivalence Theorem Revisited 285 IV. The Main Result: Another Reconstruction Theorem 287 IV. 1 Linear Growth Condition and Statement of Results 287 IV.2 Proof of Theorem £'->#' 288 V. The Analytic Continuation . 289 V.I Real Analyticity 291 V.2 Towards the Real World 293 VI. The Temperedness Estimate 297 VI.1 From Distributions to Functions 297 VI.2 Continuing the Estimates 301 VII. Appendix 303 References 305 

I. Introduction 

The passage to purely imaginary times has proven to be an extremely powerful tool both for the construction and for the discussion of relativistic quantum field theoretical models 1. Obviously for such a procedure to make sense it is important to know how to go back again to real time. In a previous paper "Axioms for Euclidean Green's functions" [12] (henceforth quoted as OS I) we claimed to have found necessary and sufficient conditions under which Euclidean Green's functions have analytic continuations whose boundary values define a unique set of Wightman distributions. These conditions 

* Supported in part by the National Science Foundation under Grant MPS73-05037 A01. Alfred P. Sloan Foundation Fellow.  

> 1

For verification of this assertion the reader should consult the 1973 Erice Lectures on Constructive Quantum Field Theory [19], where also references and historical accounts can be found. 282 K. Osterwalder and R. Schrader 

were (£0) Temperedness (£1) Euclidean covariance (£2) Positivity (£3) Symmetry (£4) Cluster property As it turned out, a technical lemma (Lemma 8.8) in OS I is wrong (see Remark 2 below) and at present it is an open question whether the conditions (E0 — E4) 

as introduced in OS I are sufficient to guarantee the existence of a Wightman theory. They are certainly necessary. In this paper we give two different sets of sufficient conditions. In Chapter III we replace the temperedness condition (£0) by a much stronger distribution condition (£0) and prove a new equivalence theorem: (£0), (Eί — £4) are necessary and sufficient conditions under which Euclidean Green's functions define a Wightman theory. Although E0 restores the equivalence theorem E+-+R, 

this new condition is not suitable for application because it seems to be difficult to check. In Chapter IV we therefore introduce a condition (£0') which is only slightly different from the original (£0): instead of simply assuming temperedness we now postulate that, roughly speaking, the order of the distributions S n (the Euclidean Green's functions) grows at most linearly in n, with bounds that grow no worse than ot(n\) β for arbitrary α and β. We call this the "linear growth condition". Assuming (£0'), (£1 —£4) we can again reconstruct a Wightman theory with Wightman distributions $B n which also obey a linear growth condition 

(R0 f). The construction of the Wightman distributions requires two main steps: first we analytically continue the Euclidean Green's functions to complex times (Chapter V). Second we establish estimates for these analytic functions, which allow us to prove that their boundary values are tempered distributions: the Wightman distributions (Chapter VI). It is interesting to note that the analytic continuation alone can be done using the old temperedness condition (£0) together with co variance (£1) and positivity (£2). It is only because the analytic continuation of one particular Schwinger function S π involves infinitely many <3 fc

that we need some control over the growth of the order of S fc to obtain the necessary estimates. Our linear growth condition seems to be quite reasonable. It certainly .holds for all field theory models for which the Wightman axioms have been established so far and a recent result of Glimm and Jaffe [7] shows that it will also hold for a φ\ model, provided it exists, and if the two point function is a distribution in «9"(IR 8

). 

Remarks. 1) The proof of Lemma 8.8 in OS I was first questioned by Simon [16]. Subsequently one of us (R.S.) found the following counter example: F(x, y) 

= exp(—xj/), x>0,j;>0 is the Laplace transform of a tempered distribution in each variable separately, but not jointly. 2) A preliminary report of the results of this paper was presented by one of us (K.O.) at the 1973 Erice Summer School on Constructive Quantum Field Theory, see [13], p. 71. It should be pointed out that condition £0' in [13] was a linear growth condition on the difference variable Euclidean Green's functions. Condition £0' of this paper refers to the Euclidean Green's functions directly; it is more general, more natural and certainly more convenient for applications than £0' in [13]. Axioms for Euclidean Green's Functions II 283 

3) The construction of the analytic continuation of Schwinger functions which satisfy £0, Eί, and E2 was found simultaneously by Glaser [6], who also eastablished the connection with his earlier work [5] on the interplay between positivity and analyticity. He too noted that in order to prove temperedness on the boundary of the analyticity domain an assumption stronger than £ 0 seems to be necessary, but he remarked that E0—E4 lead to a modified Wightman theory with vacuum expectation values which are hyperfunctions but not necessarily tempered distributions. 4) Nelson's axioms [11] imply the Wightman axioms and hence by OS I also E0—E4. It is also easy to derive E0 — E4 from Nelson's axioms directly; the crucial step is to prove positivity E2 using the Markoff and the reflection properties, see [19], p. 104. E0' seems to be related to Nelson's "scale condition", see Nelson [11]. On the other hand, to derive Nelson's axioms from £0', Eί — E4 

one has to introduce additional assumptions, see Frόhlich [3] and Simon [15]. Nelson's axioms are more restrictive than £0', £ 1 — £4 and thus lead to a richer structure. On the other hand they seem to be harder to work with in constructive field theory: for none of the non-trivial models, constructed so far, has the Markoff property of Symanzik and Nelson (Relation (1) in [11]) been verified. 5) Though in this paper we deal with the theory of one real scalar field only, the results can be extended in an obvious way to theories with a denumerable number of arbitrary spinor fields, see Chapter 6 of OS I. 6) With the obvious changes the connections between subsets of the axioms for the Euclidean Green's functions and subsets of the Wightman axioms are as discussed in OS I. 7) Constantinescu and Thalheimer have extended the scheme of axioms £0/£0', £1 - £ 4 to Jaffe fields [1],                    

> Acknowledgements. We thank Prof. A. Jaffe and Prof. K. Pohlmeyer for helpful discussions and Prof. V. Glaser for sending us a copy of his paper prior to publication. We also thank Prof. G.-F. DelΓAntonio for his warm hospitality at the Universita di Napoli, where part of this work was done.

II. Notations 

In this section we introduce some (partially new) notation and restate a few technical results from OS I. Unless stated otherwise, x denotes a point in IR 4 with coordinates (x°, x 1, x 2 , x 3 )ΞΞ(X°, X). A point in IR 4" will be written as       

> X=( X 1 ? . . . X π) ,

For integrals we write J . . . d 4 M x or simply J . . . d We will use the following open sets  

> IR 4
> . = { X G 1 R 4
> | X ° > 0 }

IR 4

." = = {xe1R 4 M 

|X;Φ xj for all 1 ^ i<j^n} 

<C + = { z e C | R e z > 0 } <C" + = {(z i9 . . . z B ) | z j e C + for all7= 1, ...n} .284 K. Osterwalder and R. Schrader 

On the Schwartz space ίf (lR m

) we will work with the following norms 1/1,= sup \(ί+xψ 2

(D«-f)(x)\, (2.1) 

> xeR m

where peΈ + = {1,2, ...},/e<9^(IR m

). We use the standard multiindex notation:        

> mm(f) \α'm

α-(α 1 ,...α m );|α| = Xα ι , Z ) ^ Π I T - * 2 = Σ (*/)*•    

> 11\Ox i/ 1

By 5^ 0(1R 4

") we denote the topological subspace of ^(IR 4

") of all those functions which together with all their derivatives vanish on the complement ~lRo" of IR 4". As in OS I we denote by © π(x) the Euclidean Green's functions and by 2B n(x) the Wightman distributions. The "difference variable" Euclidean Green's functions and Wightman distributions W^_i(£) are formally defined by 

6,(20 ^S,-!® 

respectively, where ξk = xk+1 — xh, k= 1, ...w — 1. The Wightman axioms will be labelled as follows: (RO) Distribution property, (JRI) Relativistic invariance, (R2) 

Positivity, (R3) Local commutativity, (R4) Cluster property, and {R5) Spectral condition. 

The remainder of this section will be needed in Chapter III only. 

For 0 an open set in IR m, £f(β) denotes the subspace of ^(IR m) of functions with support in O, given the induced topology. The dual space of the topological quotient space ^(lR m )/^(O) is the polar of 5^(0), which is the set of all tempered distributions with support in ~ 0 . By ίfφ) we denote the set of C 0 0 functions on O which decrease strongly with all their derivatives as |x|->oo in 0 and whose derivatives all have a continuous extension to the closure O of O. On £f(O) we define a topology by the norms 

\g\ p,o=sup\(ί + xψ 2(D a-g)(x)\: (2.2) 

> xeO

is of coursejiot a subspace of ^(IR" 1), but as the following^ lemma shows, an element in £f(O) can always be regarded as the restriction to 0 of an element in 

Lemma 2.1. Let 0 be an open set in lR m. Then £f(d) is isomorphic to 

This lemma follows from the fact that the set of functions /+ in Sf{jΰ) which are restrictions to 0 of functions fe 5^(IR m) is dense in &Φ) and from Whitney's extension theorem, see Whitney [21], Hormander [9], Vladimirov [20] and also Lemma 8.1 in OS I. From Whitney's extension theorem it follows immediately that the norms 

^o=Jn ίd) \9 + hl p (2.3) 

are equivalent to the norms defined by (2.2), (g e Sf (1R W

)) In particular, for 

O = V+ ={x\xf>0 and (x?) 2 >x?, all i= 1, ...w}, we have the following Axioms for Euclidean Green's Functions II 285 

Lemma 2.2. Suppose f +e6f(V£) and peΈ +. Then there exists a function g e y{p) 

(lR* n

) such that g(x) = f + (x) for xeV* and 

> P

,v?ύ\\g\\ P,v?ύy\f +\2 P,v? (2.4) 

with y = γ(n, p) = [c2 n

(p + l ) ] 2 p + 1 

for some constant c independent of n and p. 

Here ^ (/?) 

(IR 4

") is the closure of ^(IR 4

") in the topology defined by the | | p-norm. Notice that the first inequality in (2.4) is trivial. The second one is a sharp form of Whitney's extension theorem and follows from a detailed analysis of the proof given in [9]. We omit the details. As an easy consequence of Lemmas 2.1 and 2.2 we get 

Lemma 2.3. Let W be a distribution in <S^'(IR 4") with support in V" such that Then W also defines a distribution in <9*'(F+), again denoted by W, such that for allf +e.nVΪ) \W(f +)\S W-7\f +\2 P,v?, (2.5) 

with γ as in Lemma 2.2. 

For fe ^(IR 4") and g e IR 4" we define 

f{g) = J exp [- Σ (q°x° - ίqjx^ f(x) d*»x . (2.6) 

The following lemma follows immediately from Lemma 8.2 in OS I. 

Lemma 2.4. The map f^f defined by (2.6) is a continuous map from ^(1R 4") 

to 5^(IR 4") with dense range and trivial kernel. 

Now we define 5^(1R+") to be the linear space Sf (lR+ n) equipped with the topology given by the family of seminorms I / I > l / W , p = l , 2 , . . . . (2.7) Note that S?φϊ?) is not complete. By Lemma 2.4 the topology of S?(JR% n) is weaker than the original topology of y(IR 4 n ) and hence 

? % n ) . (2.8) 

III. The Equivalence Theorem Revisited 

In this section we introduce a new distribution property (£0) for the Euclidean Green's functions and prove that ϋΓθ together with E1 — £4 is equivalent to the usual Wightman axioms. The new condition is as follows -e^ΌOR 4

"), <S O=1 

^ e ^ ' ( K ^ ) , n = l , 2 , . .

Theorem E<->R (revisited). The conditions E0, E1 — E4 for the Euclidean Green's functions are equivalent to the Wightman axioms R0—R5 for the Wightman distributions. 286 K. Osterwalder and R. Schrader 

Although £ 0 restores the equivalence theorem £<-•£, this new condition is not very satisfactory from the point of view of applications. In praxi the continuity of Sn_i with respect to the | | p-norms is a condition which seems to be difficult to check; as we shall see below, £ 0 immediately implies that Sn_1 is the Fourier-Laplace transform of a distribution Wn-ι that has the desired support properties. From the point of view of constructive quantum field theory the results of the next section will be the crucial ones. We now turn to the proof of Theorem £<-•#. The derivation of EO, Eί — E4 

from the Wightman axioms follows the arguments of OS I; all that remains to be verified is the additional condition Sn_1 e^'OR^"' 1 *)- As in OS I, Chapter 5, we show that for fe ^{R%% Sn.ί(f)=W n.ί(f) 9 (3.1) where Wn-ι is the Fourier transform of Wn-l9 interpreted as a distribution in ^'(01+"), see also Lemma 2.1. This implies that for some /?, 

## \S n-Λf)\<\ff P (3.2) 

and hence £„_! is an element in e$^'(IR+ ('I~1) ). Let us give an alternative and simple proof of (3.1)/(3.2). For ξ eIR+ (π ~1) , the function   

> jjj
> 7 = 1

is an element of ^ ( K " " 1 ) , depending continuously on ξ. Thus by Lemma 2.3 we may write Sn_ι(ξ) as S π _ 1 ( έ ) = » ; . 1 ( Λ J ) . (3.3) Then for fe ^(IR+ ( "~ 1 } ) with compact support we define 

> 1

>ζ 

the right hand side of (3.4) being taken as an ordinary Riemann integral. We now claim that for such / 

SW n-. 1(h i)f(ξ)d«»-1) 

ξ = W n_ί(f), (3.5) which proves (3.1) for a dense set in ^ O R ^ " " 1

* ) by continuity. For a proof of (3.5) we w r i t e / a s and approximate it in ^ ( F + ) by Riemann sums. Now we show how to modify the proof of E-+R. Starting from £„_ x e ^'(]R% n

)

we define Wn_ 1 by (3.1). This defines Wn_ ι on a dense set of £f 0Rt") - see Lemma 2.4 - and_by assumption JEΓO, Wn-γ is continuous with respect to the topology of ^(IRt"). Hence Wn.ι has a unique extension to a distribution in ^'0RV) The proof of the remaining Wightman axioms now proceeds as in OS I. Equations (3.3)/(3.4) are easily verified, which shows that the Sn are indeed the Euclidean Green's functions of the Wightman theory thus obtained. Axioms for Euclidean Green's Functions II 287 

IV. The Main Result: Another Reconstruction Theorem 

IV.ί. Linear Growth Condition and Statement of Results 

As we have shown in the last chapter the equivalence £<-•# can be established if we are willing to introduce the distribution property £ 0 for the Euclidean Green's functions. In this chapter we show that we can avoid £ 0 and the | | -norms altogether. A sequence {σ n}neΈ+ of positive numbers is said to be of factorial growth 

if there exist constants a and β such that for all neΈ + . 

We now define what we call the linear growth condition for the Euclidean Green's functions. 

(£00 

S o = 1, S n e 5^o(IR 4n ) and there exist s e Έ + and a sequence 

{σ n} of factorial growth, such that 

## !©„(/)! ^ σ J / U (4.1) The following condition is slightly stronger than £0'. S o = 1, S M G Sf' (1R 4") for all n e Έ +, and there exist seΈ + and a (£0") sequence {σ n} of factorial growth such that 

(4.2) 

The following theorem contains the main result of this paper. 

Theorem E' (or E")-+R'. a) A sequence of distributions {δ n}^° =0 satisfying 

£()' (or E0") and £1 —£4 is the sequence of Euclidean Green's functions of a uniquely determined Wightman quantum field theory. 

b) The Wightman distributions {2BJ of that theory satisfy all the Wightman axioms R0—R5 and in addition (Rθ f)there exists wEΈ + and a sequence {ω n} with 0 < ω n ^ a β " 2

for some constants α, β and all neΈ +i such that 

(4.3) 

Remarks. 1. As £0" implies £0' (see Appendix) it is sufficient to prove E'-*R'. 

It is however worth noticing that a direct proof of E" ^R' would be much simpler that the proof of E'^R 1 presented in this paper. This will be explained in the introduction to Chapter V. Clearly, £0' does not imply £0". Superficially speaking, while £0" requires Sw (x 1 ...x π ) not to grow faster than Π ( ^ + : x 

? ) s / 2 

f° r

values of the arguments, £0' allows for a growth of the order of (\ + ]Γ xf\ ns/2 9  

> \ίI

and similarly for the singularities of (

Zn at points of coinciding arguments. 288 K. Osterwalder and R. Schrader 

2. In constructive quantum field theory £0" holds for all models for which £0— £ 4 has been verified so far, see Glimm, Jaffe, and Spencer [8] remark below Theorem 1.1.8, and Frohlich [3]. It is also reasonable to expect that £0" holds for models that live in the real world with three spatial dimensions: a recent result of Glimm and Jaffe [7] shows that in a (φ 4

)4 model £0" would follow essentially from the fact that S 2 is an element of 5^(IR 8

). 3. Our methods do not allow for a factorial growth estimate on ωn in R0 f

.

On the other hand, assuming R0\ R 1 - R5 and ωn of factorial growth, we can derive £(y, £1 — £ 4 ; but the bounds we obtain for σn are of the form aβ" 2. This follows easily by first applying (2.4) on hξ in Relation (3.4) and then using arguments of OS I with a sharpened version of Lemma 2.2 in OS I. Were it not for the obstacles of establishing the factorial growth bounds on σn and ωn respectively, one could again prove an equivalence theorem E'+->R f.IV.2. Proof of Theorem E'-^R' 

In this section we explain how to reconstruct the Wightman distributions from a given set of Euclidean Green's functions satisfying £0', £1 (Euclidean invariance) and £2 (positivity) and verify the distribution property R0 f. The remaining Wightman axioms can be established as in Sections 4.2-4.5 of OS I. The proofs of the theorems stated below will be given in subsequent chapters. The existence of the Wightman distributions follows from an inductive construction of the analytic continuation of the Euclidean Green's functions and from bounds on these analytic continuations which are established inductively too. We always assume that we are given a sequence of Euclidean Green's functions {©„} satisfying £0', £1 and £2. By Sn_1 we denote the difference variable Green's functions. The initial step in our inductive procedure is to prove the following theorem. 

Theorem 4.1. (A o) Real Analyticity: There are functions Sk(ζ) = S k(ξ + ir[) analytic in some complex neighborhood of IR+ k such that for all fe k

d* k

ξ. (4.4) 

(T£ o ) Temperedness Estimate: The functions S k(ξ) satisfy 

# \S k(£)\ £ xk [(l + max \ξή (l + £ ξή (l + ££ ή ( £ (4-5) 

for some sequence τ k of factorial growth, some positive integer t (not depending on k) andallkeΈ +,allξe1RX k.

In the r'th step of the induction we construct open subsets C[ r) ofC+ and prove the following theorem. 

Theorem 4.2. (A r) For fιxedj={ξ u ...ξ k) the functions Sk(ξ° \ξ) = S k(ζ) have 

an analytic continuation Sk{ζ°\ξ) to the region ζ° = ξ° + iff e C {k\ Sk(ζ°\ξ) is 

continuous in the variables ξ. (TE r) For ζ° e C^ and ξe R 3 k 

the functions Sk(ζ°\ξ) satisfy 

# ί° ll)| ^ c fc ffl + max iξ ή ^ + Σ 1^0 ί 1 + Σ ( R e φ - ^] f c ί ' (4.6) Axioms for Euclidean Green's Functions II 289 

for some sequence c k, such that c k ^ aβ k

for some α, β > 0, some positive integer t\ not depending on k and r; and all k = 1, 2,... . The subsets C[ r) 

are increasing: Ckr) 

cC kr+1) 

; Ck°}

is just the k fold product of the positive real axis and most importantly, the union (J Ckr) 

of all 

> r

the subsets is all of C+. Parenthetically we remark that only the bounds TE r

require the linear growth condition (4.2). For the other results the original temperedness condition (EO) of OS I is sufficient. The final result of our induction is summarized in the next theorem. 

Theorem 4.3. There are functions Sk(ζ°\ξ), analytic in the variables ζ°, con-tinuous in the variables ξ for ζ°e<C+ and ξ e IR 3fc , such that (4.4) and (4.6) hold. 

By standard arguments (see Vladimirov [19], p. 235ff.) Theorem 4.3 implies that there exist unique distributions Wke & ?'(lR 4'k) with support in lR+ fc such that Sk

are the Fourier-Laplace transform of them: 

# = ί ) j

As in OS I we conclude that Wk is the Fourier transform of the difference variable Wightman distribution Wk.

Furthermore, again using (4.6), we find that for he 

= hm ΪS k(η 0

+ iξ°\ξ)h(ζ)d* k

ξ   

> η9-*0+ ~~~

satisfies the inequality 

\W k{h)\ύW k\h\ kt .. (4.7) for some sequence Wk^a\β') k2 and t" = — -+5, see Vladimirov [19], p. 235, Eq.(14). 

It remains to derive R0' from (4.7). Let fe ^ ( I R 4 " ) a n d set hXί (ξ) = f(x u x2...x n)

where ξk = xk+ι — xk for k= 1, ...n— 1. Then 

^<-iί\K ί\kt"^x 1^ω n\f\ kt '" 

for some new sequence ωn g α"(/?")" 2 and t'" = t" + 4. This concludes our proof of 

Theorem E' ->JR'. 

In the remaining chapters we explain the inductive procedures in detail and prove Theorems 4.1 and 4.2. 

V. The Analytic Continuation 

In this chapter we construct the analytic continuation of the Euclidean Green's functions to "real times" and prove (A r) for r = 0,1, 2,.... No use will be made of the linear growth condition EO' at this point; all we assume for the moment is EO, Eί (invariance) and E2 (positivity). 290 K. Osterwalder and R. Schrader 

As we have seen in Section IV.2 we have to analytically continue S fc (ξ) = Sk(ξ° | J) in the "time variables" ξ° only; the "spatial variables" ξ_ play the role of parameters. There are two different ways of dealing with the spatial variables in a rigorous fashion: 

Method A: To treat the spatial variables as distributional variables throughout. More precisely for fik e ^(IR 3 ) and fn = (f ln9 . . . , / J we define with ξ? = x? +1 - x?, Positivity will play an important role in this and the next chapter, and S π_ 1 (ξ° \J) 

was defined such that it still satisfies a positivity condition: for all finite sequences {h 0, hl9 ...},h oe<£,h ne ^(1R M+) and all fik e ^(IR 3 ), where 

SJ nχJ m is the function 

Jnn\ X\)"' Jln\ Xn) Jίm\ Xn+l)'"Jmm\ Xn + m) •> 

χnr \ ίθ — tμO μO μθ\      

> a n α ς —{ζ n-ί9 ζn~2>•••C i λ

Method B: To show that Sk(ξ° 11) can be regarded as a continuous function of the spatial variables; this makes smearing out redundant. Method A was sketched in [13]. It is simple, mainly because it allows for the reconstruction of the Wightman distributions without using S O 4 invariance of the Euclidean Green's functions. The drawback of this method is that in order to derive a temperedness estimate for the analytically continued Euclidean Green's functions, we need a distribution assumption slightly stronger than £0', such as 

E0". Though it is true that E0" is most probably satisfied in all reasonable quantum field theory models - see Glimm and Jaffe [7] - the weaker assumption 

E0 f is more satisfactory from an axiomatic point of view: besides being more general it does not make use of coinciding arguments of the Euclidean Green's functions. This justifies our use of the more complicated method B in this paper. Extending a geometrical argument of Glaser [6] we use S O 4 invariance to prove that the Sk are real analytic functions in all variables. Then we derive a tem-peredness estimate for these functions from their behaviour as distributions. Let us first summarize some results of OS I (in a slightly changed notation). In terms of the difference variable Euclidean Green's functions Sk the positivity axiom E2 requires that for all finite sequences {f θ9 fuf2> •••}> /o G

^»/« G

^(^% k

)

(5.1) 

where ξ = (ξ u...ξ n_1),ξ' = (ξ' u...ξ' m_1),H = (Hi,:.H n-1),$ξ k = (-ξ° k,ξ k) and 

finally J = ( ί B _ 1 , . . . ί 1 ) . As in OS I we construct a Hubert space Jf and furthermore j f -valued distri-butions Ψn(x,ξ) such that for / e ^flRΐ"), g ewith scalar product Axioms for Euclidean Green's Functions II 291 

or, in the sense of distributions, 

(Ψ»(x,ξ\ Ψ m(x\ξ')) = S n+m _1(-$ξ, -Sx + x' 9£). (5.2) The set of vectors ΨJtf)Je£fφX n\ n = 0, 1, 2,... (for n = 0J must be in C, of course) is total in Jf .By the arguments of OS I, we can construct a weakly continuous semigroup of self-adjoint contractions e~ tH on Jf, t Ξ> 0, H = H * ^ 0, such that (in the sense of distributions) e-'«Ψ H(x^) = Ψ H((x 0 +1, x),ξ) . (5.3) Furthermore for τ e <C+ = (0, oo) + iIR 

(W n(x^le^ H

TJx\n)^S n+m .A-HAx° + xOf 

+ ^~x + n^) (5.4) 

defines an analytic continuation oϊ S n+m _1 in the n'th time variable: by OS I the right hand side of (5.4) is an analytic function of the variable z = x° + x 0 ' + τ for Mez>0, while still being a distribution in all the remaining variables. (It was at this point in OS I that the wrong Lemma 8.8 was used to continue Sk

in all the time variables simultaneously to the /c-fold product of <C+.) In the following we use (5.4) and Euclidean covariance £ 2 to show that Sk(ξ) is the restriction of a function S fc (ζ), analytic in a complex neighborhood of IR+ k, i.e. assertion (A o). V. I. Real Analyticity 

For 0 < γ < π/4 we define 

Uy) {χ (χ,χ)\χ>\ 

and Rΐ Π(y) = {2c = (x 1 ,...x Π )|x f c elRί(y),/c=l,...w}. Obviously 1R+ (y) is the largest cone in IR+ which under an arbitrary rotation 

0t{a, φ) about an axis a through the origin, by an angle φ :g y, stays in IR+. Euclidean covariance implies that for any ξ e IR+ fe (y) and 0 ^ φ ^ γ

Sk(a(a,φ)£) = Sk(£) 9 (5.5) 

where Λ(α, φ)ξ={Λ{a, φ) ξ l9 ... @{a, φ) ξ k). 

For fixed ye(0,π/4) let eμ = e μ(γ) 9 μ=ί,...4, be four linearly independent vectors in 1R+ (π/2 — y\ the dual cone of IR+ (y). Then there are rotations ^ μ = βl(a μ, φ μ) with 0 ^ φμ < y such that Λ Λ = (l,0,0,0). (5.6) Now let ξe]R\ k

(y) be fixed and u = (u l9 ... uk), where u( = (uf,uf 9uf,uf) 9 

> 44

wfe[0,oo). Writing u e for the vector \Σ u

ϊeμ> •••Σ u

ke

β] i n 

R ? ( π / 2 - y ) we now consider ^ ^as a distribution in the variables w {J. By (5.5) we find that for μ = 1,... 4 Sf c (| + M β)= S Λ ( Λ μ | +u ^ μ e ) , (5.7) where 01 μe stands for the four vectors ^ μ e v , v = 1, ...4. By (5.4) and (5.6) the right hand side of (5.7) can be analytically continued to < C+ in each of the variables 

uf , i = 1,... k9 (one at a time), while it is still a distribution in all the other w-variables. 292 K. Osterwalder and R. Schrader 

oNow we pass to variables sf = lnuf and set T(s\, ...st) = Sk(ζ + u e). According to the above argument we can find functions which are analytic in rf = sf + it$, \tf\ < π/2, and have values in & with respect to the variables s}, . . . $ , ...sj. All the Tiμ analytically continue the same dis-tribution f. It follows now from the Malgrange-Zerner theorem, see Epstein [2], which deals with a degenerate case of the well known "tube theorem" (see e.g. Vladimirov [19], p. 154), that there is an analytic function Γ(r)=Γ(ri,...,rί) analytic in the convex envelope &~ of the union of all the flat tubes such that T continues all the Tiμ . We find that ZΓ = \r\, ...r£|£|Imrf|<7r/2J. I i,μ iGoing back to the variables uf and to S we have therefore shown that there exists a function oanalytic in ^ ~ ~ (5.8) 

## jw|Σ|argwf|<π/2l, o owhose restriction to real arguments defines the distribution Sk(ξ + u e\ with ξ

and eu .. . e4 playing the role of fixed parameter. Assertion (A o) is now an immediate consequence. For the benefit of Section VI. 1, where we establish the bound (7Έ 0 ), we now derive an estimate on the size of the region of analyticity of the function Sk(ζ) 

obtained above. 

Lemma 5.1. For fixed ξelR+ k, the functions Sk(ζ + ζ) are analytic in the poly disc Γ(£) = {ζ\\ζϊ\£Q,for l£iZk,l£μZ4}, where ckfor some constant c e (0,1) independent of k or ξ. 

o

Proof. For given ξ we define y and ξ by tg2y= min ξ°j/\ξj\ and ^ ^ k (5.10)                

> 0000io~"
> |= ( I I J IΛ)> ^ = (ϊίf > ίί)» l^i^k,
> and we choose the vectors eu...e 4as follows: β1= ( 2 c t g y , 1,1, 1)

. , - ( 2 . ^ 1 , - 1 , - 1 ) e3 = (2ctgy,-1,1,-1) β4 = (2ctgy,-1,-1,1). Axioms for Euclidean Green's Functions II 293 

Obviously 0 < y < π/4, ξ e HR.% k{y), eμ e R f (π/2 - γ) and eι,... e 4 are linearly independent. (5.11) implies (l,0,0,0) = 2-3 tgy(e 1 +e 2 + e3 + e 4)(0,l )0,0) = 2 - 2 ( e i + e 2 - e 3 - e 4 )

(0,0,i,0) = 2-2

(e ι-e 2 + e3-e 4)

(0,0,0, l) = 2 - 2

( e 1 - e 2 - e 3 + e 4)and 

ξ, = l + 2-*ξ?tgy Σ eμ

ξι + ζι = l+ Σ (2-4ξftgr + 2-3tgyζ? + 2-2 £ > r μ ί ϊ W (5.12)   

> μ=l\ r=l I
> μ = l

where σ r μ is equal to 4-1 or — 1 and may be read off Eq. (5.11'). It follows from (5.8) that Sk(ζ + ζ) is analytic for those values of ζ for which £ |argwf|<π/2. It 

> i,μ
> 71

therefore suffices to assume that for all i, μ |arg wf | < -^377, which is implied by By (5.12) the wf are given as functions of the £?, and (5.13) is satisfied if we restrict if by ^ 5 ^By (5.10), t g y < i t g 2 y = i min (^/|ζ|) and hence Sk(l; + ζ) is analytic if 

m<^ Iξΐ-rmn(ξy\ξ J\). (5.14) This implies Lemma 5.1, with c = 2~ 9

π. V.2. Towards the Real World 

Having established the real analyticity of Sk(Q we now proceed to construct the analytic continuation «S k(C° \ξ) of Sk in the time variables to the ra-fold product of <C+. (Notice that iζ° n are actually the times, hence at the boundary of <C+ we will arrive at real times.) Our method is to verify inductively the following sequences of statements: 

(A N) There are analytic continuations Sk(ζ°\ξ) of Sk(ξ°\ξ), which are continuous in ξ e 1R 3k

and analytic in ζ° e C{kN) 

C <C k

+. For N = 1,2,..., C{kN) 

is the envelope of holomorphy of  

> (5.15) 294 K. Osterwalder and R. Schrader

(P N) There are Jf-valued functions 

Ψn(x°,ζ°\x,ξ) 

defined for (x,f)eIR 3" and (x° iζ°)eD^ )C(0 9 oojxCV 1 , where for JV=1,2,... 

D^ = {(x^C°)|x°>0,(? ?2Λf)eC^_ 1}, (5.16) 

such that the scalar product is given by (5.17) Notice that the passage from N — ίto N takes place in (5.15), where C[ N) is defined in terms of the regions D^"^. Later we will show that \J Cjf ) = <C+, which completes the analytic continuation. N

In the rest of this chapter the spatial variables will always play the role of parameters and we therefore drop them completely in our formulas. Continuity with respect to them will be evident at each step. Also we will drop the super-scripts °, hence ζ will now stand for (£?,... ζ£), etc. To start the induction we set ..fc}, (5.18) 

OJ=U...n-ί}. (5.19) Then (A o) follows from the results of Section V.I. We claim that (P o) follows from 

(A o) and (5.2). Notice that (5.2) was valid in the sense of distributions only, while (P o) asserts that it also holds in the sense of functions, i.e., pointwise. For a proof smear both sides of (5.2) with two functions fv e Zf (R% n), g v e ^ 0R+"), which as v tends to infinity tend to δ-functions and take the limit. Now assume (A N) and (P N) have been verified for 0 ^ N ^ M — 1. We will prove (A M) and (P M). By (P M _ y) we can define for (x,ζ) e D{nM

~υ

and (x\ζ f

) e D^' 1] 

\ this analytically extends Sk, k = n + m - 1, to C(kM) 

and hence, because C[ M) 

is the envelope of holomorphy ofC[ M

\ there is an analytic extension of Sk into CkM

\ This proves (A M). 

Now take a point (x,ζ)eD {nM

\ defined by (5.16), and observe that with (x 9ζ) 

othe whole cone of points of the form (x 9ζ) with x > 0 , |argζ x | ^ |argC t-|, i= 1, ...n— 1, is contained in D{nM

\ We therefore can find points ξt e (0, oo) and numbers r f > 0, such that the whole polydisc 

P={(x,ζ)\x = l\ζ i-ξ i\<r i9 i=i,...n-i} 

is contained in Z)^ M) 

and (x,ζ) e P, see figure below. o ° Now we define the vector Ψn(x,ζ) by 

# ^ i ^ (520) Axioms for Euclidean Green's Functions II 295 

complex ζ\ - plane 

Fig. 1

where the derivatives of the vector Ψn are taken in the strong Hubert space topology. The right hand side of (5.20) converges in norm, for 

# ii d-ξr-/dw ψ\{χO j2

> ί < W

o o , (5.21) and the right hand side of (5.21) is just the remainder term of the Taylor expansion     

> 0Q0<-Q

of S 2 n _i(C, 2x,C) about the point (|,2x,^) and thus tends to zero as we let t

go to infinite. Relation (5.17) follows easily from (5.20). This establishes (P M). Finally we have to prove that (J Cψ ]

= C+. But this is a consequence of the following stronger result, which we will need in Section VI.2. 

Lemma 5.2. For allN,n,keΈ+, 

(a) D(nN) 

contains the set 

(b) C(kN) contains the set where and Proof. By construction the regions C£ N) and D{"] are mapped onto tubular domains under the transformation ζi = eWί = e Ui+iVi . We define 4N ) and 4 N ) t 0 

be the closure of the bases of these tubes: 

, i^i^k,{e wl ...e Wk )eC{ N) } (5.22) 

Note that 4 N ) and df * are subsets of [- π/2, πβf and of [- π/2, π/2]" respectively. 296 K. Osterwalder and R. Schrader 

From the inductive definitions (5.15/16), (5.18/19), and from the tube theorem we find for r= 1,2... 

ckN) = convex hull of 

{v\v = (-v\ v, υ"\ where (0, v') e df~ ι\ (0,/)e d^W , \v\ ύπ/2) (5.23) 

4"MMK-£,0,iOe4Ti} (5.24) 4 0 ) = {(0,...0)}, rf<°> = {(0,...0)}. (5.25) 

Observe that all the sets c[ N) a n d ^Λ V) a r e convex. Moreover if (v l9 . . . ^ e c f 1

(or ^ N ) ) , then the whole hyperrectangle with corners (±v ί9 ... ±v k) is also con-tained in ckN) (4 N ) resp.). For a proof of Lemma 5.2 we show inductively that the points (0, vl9 ... ι^ n_i) with |t7 £| = = ^(/, iV) are in d{^\ This establishes part (a); part (b) follows from (a) and the equation Sk(ζ) = (β, Ψk+1 (x,Q) 

We first construct a function ftf, i = 1,2,..., JV = 1,2,..., such that for all  

> s

= ° f = *' w»( s,t ) = (O^O^O, A?,ΛJ,...Λ?)e d}!?,. (5.26) 

> t

We choose Λ? = 0 for all i. By (5.25), w°(s, t) e d\°^ s. Suppose now we have already constructed hf for all i: ^ 1 and N = 1,... M, such that (5.26) holds. Then by (5.23) the following points are contained in c^+J/.j 

## (_ hf,...-fcf,- /if, 0 ^ 0 , π/2,Λf, .../zf_ x)

> 2 ί - l

and (-/if_ t -/if, - π/2,0^,/if,/if,.../if). 

> 2 ί - l

Because c^+o-ik convex it also contains the point 

> 2 ί - l

This means [by (5.24)] that with i(Λf+ π/2) (5.27) W + ^ i ) , 1 = 2,3,... the points w M + x(s, t) defined by (5.26) are again in d{%s+ υ .We take (5.27) as inductive definition of /if. A simple calculation shows that the solution of (5.27) is From (5.26) we now conclude that in particular all the points w > - l , l ) = (0,/ιί,.../i^_ 1)are in d^\ This ends the proof of Lemma 5.2. Axioms for Euclidean Green's Functions II 297 

For later purposes we remark that ρ(i, N) ^ -y (1 - 2~ N/2 

yi\ where (5.28) Hence (b) of Lemma (5.2) implies the following corollary. 

Corollary 5.3. C{kN) 

contains the set 

^ m a x |θ, y ( l -

VI. The Temperedness Estimate 

In this chapter we derive the estimates (4.6) for the analytic continuation Sfc(C°|£) of the Euclidean Green's functions. It is at this stage only that we have to use the linear growth condition. We point out that using £0" instead of £0' would simplify and shorten our argument considerably. In a first step we derive from (£0') the temperedness estimate (4.5) on the real analytic functions Sk(ξ). This is the most complicated part of this chapter and it will be discussed_in Section VI. 1. The estimate (4.6) for the analytically continued functions Sk(ζ°\ξ) will be proven by induction in Section VI.2. 

VI. 1. From Distributions to Functions 

At a first glance it might look rather trivial to derive an estimate of the type (4.5) from £0' and from the fact that Sk(f) is given by the ordinary Riemann integral lS k(Qf(ξ)dξ, with S ^ e C 0 0 , say. The following example however illustrates that more detailed information about S k(£) must be available for (4.5) oto be true: Let T(x) be a positive C0 0 approximation of the function T(x) that equals exfor xe[n,n + e~ ln \ neΈ + , and that is0otherwise. Then |J T(x)f(x)dx\ S suρ|/(x)| for all fe «S"(IR), but T{x) is not polynomially bounded. In Section V.I we constructed the function Sk(ξ + ζ), analytic in the polydisc 

Γ(ξ) = {ζ\ \ζf\ < ρ} 9 where ρ was a function of ξ EJRX\ see (5.9), Lemma 5.1. By the mean value theorem for harmonic functions (see e.g. Stein, Weiss [18]) (6.1) where ΩΊ denotes the surface of the unit sphere in <C 4, ΩΊ = {ze<C 4| \z\ 2 

> 4

2 k

= £ \z μ\2 = 1} and |Ω 7 | = —y π 4 is its surface area; dΩ(z)= ]~] dΩ(z t ), where 

dΩ(zι) is the element of surface area on Ωη. Furthermore rz = (r 1z1, ...,r kzk)

with η > 0 such that Id l + * •»•<£• Here and in the following ξ and ρ = ρ(ξ) take 

fixed values. Notice that ρ is always less than 1. Let now h(-) be a positive C0 0 

function with support in β , 1] such that for some c > 0 , p > l 

\h\ nSφ\) p

and Sh(r)r Ί

dr= 1 . (6.2) 298 K. Osterwalder and R. Schrader 

Such a function h exists (for any p > 1) by the theorem of Carleman-Mandelbrojt-Ostrowski, see e.g. Mandelbrojt [10] (take e.g. k(x) = const. • e x p [ - (1 - x)~ β] with β> ). We now set for z e C 4

P~ 1/ 

gβ() \ Ί Γ ( Q

a n d 

kρ(z) = Sg ρ(z-z')g ρ(z')d 8z' 

where dsz' =d 4xfd4y',z' = x' + iy'. Hence 

suppk ρe{ze €4\\z\< ρ/4}, 

and (6.3) 

$k ρ(z)d*z=ί. 

Notice that kρ is a function of \z\ only. We therefore may combine (6.1) and (6.3) to obtain with ke(z) = f| /c ρ(z ί), 

> i

Sk(ξ + 0 = JS k(£ + C +1) fc ρω d 8*z, (6.4) 

whenever |ζ f | <ρ/2, / = 1, ...,/c. By Fubini's theorem the order of integration on the right hand side of (6.4) is arbitrary. We thus may define    

> ρll

x (6.5) 

such that (6.4) becomes 

Sk(ξ + ζ) = ST k(ξ + ζ + ίI)d 4k yd 4k y'. (6.6) (Notice that Tk depends on j ; and j ; ' also via kρ) Finally taking into account the support properties of kρ and of gρ we find that the integration in (6.6) goes only over the region where \y t\ < ρ/4, |y|| < ρ/8 and therefore 

\S k{ζ)\£ sup \T h(ξ + iy)\. (6.7) 

> bil<β/4 bίl<β/8

The remainder of this section is devoted to the derivation of a bound on Tk which combined with (6.7) gives the temperedness estimate (4.5). The main idea is simple. By (6.5), Tk(ξ) is a regularization of (the distribu-tion) Sk. Just as Sk9 Tk satisfies some positivity property; in other words, Tk(ξ) 

can be written as the scalar product (Ψ i9 Ψ2) of two vectors in Jf. Then (Ψ ί,e~ zH 

Ψ2)

defines an analytic continuation of Tk(ξ) in one variable (as in Section V.I), whose absolute value is bounded by || ^ || ||!P 2 ||. Bounds on | | ^ | | follow from £0'. Repeating this procedure 4fe times we obtain analytic continuations of Tk(Q in 4/c linearly independent directions. Analytic completion then leads to the function 

Tk(ξ -f ζ), the modulus of which we can estimate by using the maximum principle. This will give the bound (4.5) on Sk(ξ) by (6.7). oFor given ξ e R + we define ξ, y, 0ί μ G S O 4 and the vectors el9 ... e4 as in (5.6), (5.10/11). We use gρ(0l μx + iy) = g e(x + iyy 9 kρ(0t μx + iy,y') = kρ(x + iy,y') and Axioms for Euclidean Green's Functions II 299 

we simply write gQ(x) and kρ(x) for gρ(x + iy) and kQ(x + iy, y') respectively. Then using Euclidean co variance and (6.5) we find for all u\ ^ 0, and lrgrc^/c, l ^ μ ^ 4 , 

g() (x')k Q(ξ'-λ f

)d* in 

-1) 

ξd 4{k 

-n) 

ξ'd 4

xd 4

xf

. (6.8) Here λ = (λ u ...^-x) and 2' = (λ n + 1 , . . . 4 ) , where X^M^ + u^eeR 4- and 1 ^ n rg /c. For later purposes we remark that 

^2ξ 2 + 2(4ctg 2y +3) Γ^uf] 2, by (5.11) (6.9) ^ const, ρas c t g y ^ 2 ( l + c t g 2 y ) ^ 2 c ρ ~ 1 by (5.9) and (5.10). oEquation (6.8) exhibits Tρ(ξ +ue) as the scalar product (Ψ u Ψ2) of the two vectors 

# j

## and J' 1 (6.10) 

As in Section V.I we find the analytic continuation of Tk in the variable uμn

by sandwiching e~ iv "H between Ψγ and Ψ2' for we^ nμ , where [ = 0 for ί + n or/and v φ μ } , - i ι ; 

" H

ϊ r

2 ) ϊ and (6.11) 

W, uniformly in rJJ. We defer the proof that by E0' for some sequence σn of factorial growth, 

# l l 1 l l ^ n ρ (

# /

and correspondingly for || Ψ21| with n being replaced by k — n + 1 and 

\

by Σ λ

f) Combining (6.9) and (6.12) with (6.11) we find for w e 0> nμi   

> i=n+l I300 K. Osterwalder and R. Schrader

where σk is again of factorial growth. This bound holds uniformly in the parameters j ; , y on which Tk also depends. In order to get the last factor in the expression on the r.h.s. of (6.13) we have used that 1 + Σw ' ^ |1 + Σ w Ί We now may study the functions 

rvi=\nw vi) which is analytic in the tube $~ nμ = {r||Imr{J|<π/2, Imr^ = O for ίή=n 

or/and v Φ μ} and whose modulus is uniformly bounded there by 

>2. (6.14) For Im r = 0, the functions Rl μ(r) are all equal, independent of n, μ [namely, equal to (1 +Σu vi)~ ks Tk(ζ + ue)']. Hence the Malgrange-Zerner theorem applies and there is a function Rk(r), analytic in the convex envelope ^~ of ZΓ = (J &~ nμ ,

> nμ

which continues all the ΛJ μ(r). We claim that \R k(r)\ is again bounded by (6.14) for all r in ^\ For a proof let us assume # k (r) takes a value ^ at a point r e 2Γ ~ ZΓ, 

which it does not take in ^\ Then (R^-A)' 1 is analytic in an open neigh-borhood 2Γ c & of ZΓ but not in all of ZΓ. This is impossible, because &~ is the envelope of holomorphy of # . Hence sup \R k(r)\ = suj) |-R fc (r)| (6.15) and the assertion follows. The function o7i(<ς + we) = (1 + ΣWf) κfc (lnw) analytically continues Tk(ξ + ue) to the domain ® = j w | £ | a r g w Ί < π / 2 l and it I t\ v Jsatisfies the bound (6.13) for all w e ® . oNow we go back to (6.7) and use (5.12): ξ + iγ = ξ + we, where 

> 3

~2

Σ σ

rμ/i 

> r = l

and, as tgy ^ 1, |y?| < ρ/4, \yt\ < ρ/4, Also note that (I) 2

= ( i ξ ? ) 2

+ ξf < (ξd 2

. Hence from (6.13), (6.7), and (5.9) we get (6.16) for some sequence τk of factorial growth and ί = 5(s + 8). Inequality (6.16) is the temperedness estimate (4.5). Axioms for Euclidean Green's Functions II 301 

It remains to prove the bound (6.12) on HίFJ and ||?P 2|| respectively. From (6.10) and (5.2) we get 

• gβ(-9x'-λ n) Π kβ{-H' n-i-λddxdx'dξdξ gβ{-&y n-k) n

^σ 2n - sup 

> x,y
> n - 1
> n-ί

## Σ*ί + Σyf) D/g β(x β-λ n) Π kβ(x,-x ι+1 -λ t)

• D/g β(y n - λ n)

By (6.3), the function under the sup in (6.17) is nonzero only if | x n - J . B | < ρ / 8 , | x i - x i + 1 - A i | < ρ / 4 for ΐ = l , . . . n - l 

> n

and similarly for yv This implies that |xj < \λ n\ + ρ/8, | x f | < ^ |/lj| + (w 

> J = l

and [as (M— l)ρ/4 is always smaller than 1] 

## 1+Σ*?+Σ3^8n 2

## (l+Σtf). (6-18)       

> ί = l i = l \i=l/

Furthermore by (6.2/3), for some c > 0 This together with (6.17/18) yields (6.12). This completes the proof of the temperedness estimate (4.5). 

VI.2. Continuing the Estimates 

In this section we prove the temperedness estimates (TE k) for keΈ +. In essence we will repeat the arguments of Section V.2 but carrying along the estimates on the analytic functions Sk(ζ°\ξ). Our main tool will be the maximum principle, see (6:15). In order to dispose of the spatial variables ξ we let 8& pn be the Banach space of all continuous functions on IR 3w 

, satisfying | | / | | p = _sup 1(1+ max | ί ί h " V ( θ < o o . (6.19) Then Sk(ξ°\ •) are real analytic functions in the ξ° variables, for ξf > 0, with values in Λkttk . By (4.5) (6.20) 302 K. Osterwalder and R. Schrader 

for some constants α > 0; β > 0. We write Sk{ξ°\ •) simply as Sk(ζ°) or as Sk(ξ)- thus suppressing the superscript 0. Suppose now we have already shown that Sk{ζ\ •) = Sk{ζ) defines a real analytic function from C{kN) to &kt>k . Then we define 

\k-l+ε-r kt Sk(ζ + ε), (6.21) where ε is the vector (ε,... ε), ε > 0. Now let k = n + m — 1, (x, ζ) e Dj, N) (x,ζ f)

and z = x + iye<E+. Then the Schwarz inequality 

## ||S k (5,2x,Γ)ll*^(l^^ (6.22) 

is an immediate consequence of PN, Eq. (5.17), and of the definition (6.19) of the norms || | | r Inequality (6.22) holds for S. ε as well: For k = n + m— 1, To get (6.23) from (6.22), we only have to prove that for Re £ t > 0, Re ζ\ > 0, x > 0,    

> n-ί _m - 1 \|2fc

## f Σ Ct + 2z+ Σ ίί (6.24)   

> ll/I

" " 2 m - l 

( 2 m - i)~   

> \i/

and (/c" 1 ^ ε " 1 ) 2 ^ [ ( 2 n - I ) " 1 - h ε " 1 ] 2 n - 1 [ ( 2 m - I ) " 1 + ε " 1 ] 2 w " 1 . (6.25) Clearly (6.24) follows if we can show that  

> n-l
> 11
> 2k

^r.h.s.of(6.24). (6.26) Both inequalities (6.25) and (6.26) can be brought into the form 

r + sj \ r I \ s j 

for A and B both positive; (6.27) follows from the convexity of the function 

fix) — lnx. We now claim that for ζ e C {kN

\\\S (Oil <oίk βk 

- 2βkN 

(6 28) with α and β as in (6.20). We prove (6.28) by induction. For N = 0, (6.28) follows from inequality (6.20). Now assume we have verified inequality (6.28) for N = 0, 1,... M

and for all keΈ +, all ε>0. Then for (x,ζ)eD {nM\ (x,ζ f)eD {Jf\ z = x+iye£ +,k = n + m— 1, we have by (6.23) and the induction assumption 

S [α(2n - I f 2

" " l ) 

2β{2n 

~1)M 

α(2m - i)^ 2m 

~ υ

2 ^ 2 w 

" 1 ) M 

] - (6.29) 

<ock βk 2βk{M+i) Axioms for Euclidean Green's Functions II As C[ M+1) 

is just the envelope of holomorphy of the region 

303  

> n+m— 1=k

we can use the maximum principle (see (6.15) and e.g. Vladimirov [19] p. 178), to conclude that (6.28) holds for N = M + 1. We argue first point-wise, i.e. for fixed values of the spatial variables j ; and then take the norms || || Λ f .Our final step will be to eliminate N from the right hand side of (6.28). (Notice that the right hand side of (4.6) does not depend on N either!) For a given ζe(C k

+

we want to find an N = N(ζ) such that ζeC[ N\ Choose s such that |arg£ r| :§ |arg(J for all ί^r^k. Now |argC s| + arc sin s = π/2, hence 

## ICJ ICJ 

Choose the integer N = JV(ζ) such that [with yk as in (5.28)] (6.30) Then by Corollary 5.3, ζ e Cί N) . Inserting (6.30) in (6.28) shows that  

> ifOi 2βk

<<xk βk 7 k 

## 1/2 

> 2βk 2βk

We combine this with (6.21), choose ε = to get for ζ°e<C k+,ξe JR. 3k ,

in Reζf a n d " u n d o " the n o r m || || k ί 

> kt

and 

\S k(ζ°\ξ)\^c k 

> ί

[(1 \-iγ\(2β + t)k (6.31) where ck = ak {β ~t)k (y kπ) 2βk 2{t ~β)k . From (5.28) one easily gets yk<c k for some 

c> 1, and hence ck<ab k2 for some constants α, b>0. Inequality (6.31) is the desired temperedness estimate (4.6) with t' = 2β + t. 

Appendix (by Stephen Summers) 

Theorem. Condition E0" implies E0'. Proof. We prove the equivalent statement that for R") with (Al) 304 K. Osterwalder and R. Schrader 

for all ft e ^(1R) and some fixed r, it follows that 

\T{g)\ύc n\g\ n.t (A2) for all g e ^0R W), some fixed constant c not depending on n or g and t = 2r + 7. We use a Hermite expansion for T, see Schwartz [14]. (Hermite expansion can also be used to prove the nuclear theorem, Simon [17].) Writing Ht for 

Hh®H i2 ... ®H in , where Ht is the i-th Hermite function, we get 

where i = (i u ...i n), ikeΈ +, and τ^Tity, yi = SH i(x)g{x)d"x. We set (1+j) 

= Π (1 + ifc) and obtain 

> fc=l

(A3) where c\ = ^ (1 + j) 2 = ( Σ (1 -H) 2 . To finish the proof, we have to determine 

## \ Ji = 0 

s such that |(1 +j)~ S τ /l i s uniformly bounded in j . ^" Introducing^ 1 =—^-(x kTd k), we have αfc + Hί k = l/l +ί kHik+1 and k

= ]/%H ik _u akak Hik = (ί + ί k) H ik = (t + xl~ d2k) H ik . Furthermore (dropping the index k for the moment) i| Γ = sup ||(1 +x 

^ c2 sup || x^ θ α Ht II 2 (Sobolev inequality) (A4) ^ c 3 supHα 1

. . . α 1

/ ^ ! ^ ( ^ 2 r + 1 factors α +

or a") 

Here and in the following cm denote constants that depend on r only. By (Al) and (A4), 

|Ti | = 17(^)1 ύΠ\ Hΰr 

^ ^ ( i - f - i T + 1 

. ( A 5 ) 

Choosing s = r+ 1, we dominate the second factor in (A3) by cj. Finally 

1(1 + i s + 2 

yj = ί(Π (1 + *f - Sir 2Hik {x k)\ g(χ) dx 

> k

S c" 5 sup 1(1 + x2

)" 12 

Π (1 + x\ - d 2ky+2 

g(x)\ (A6) ^ c« 6 sup 1(1 + χψ*+s+v D*-g(x)\ S c\ \g\ nt ,Axioms for Euclidean Green's Functions II 305 

where t = 2s + 5 = 2r + 7, and 

cn5 = |J(1 + x2

Γn/2 

HL(x) d n

x\ £ 

Substituting (A5) and (A6) we obtain (A2). 

+ x 2

Yn

dn

xf .

References 

1. Constantinescu, F., Thalheimer, W.: Euclidean Green's functions for Jaffe fields. Commun. math. Phys. 38, 299—316(1974) 2. Epstein,H.: Some analytic properties of scattering amplitudes in quantum field theory. In: Chretien,M., Deser,S. (Eds.): Brandeis lectures 1965, Vol. I. New York: Gordon and Breach 1966 3. FrohlichJ.: Schwinger functions and their generating functionals. Helv. Phys. Acta 47, 265 (1974) 4. Gelfand, I. M., Shilov, G. E.: Generalized functions, Vol. II, p. 227. New York and London: Academic Press 1968 5. Glaser,V.: The positivity condition in momentum space. In: Problems of theoretical physics. Moscow: Nauka 1969 6. Glaser,V.: On the equivalence of the Euclidean and Wightman formulations of field theory. Commun. Math. Phys. 37, 257 (1974) 7. Glimm, J., Jaffe, A.: A remark on the existence of φ%. Phys. Rev. Lett. 33, 440—441 (1974) 8. Glimm,J., Jaffe,A., Spencer,T.: The Wightman axioms and particle structure in the P(φ) 2

quantum field model. Ann. Math. 100, 585 (1974) 9. Hormander,L.: On the division of distributions by polynomials. Arkiv Mat. 3, 555 (1958) 10. Mandelbrojt,S.: Series adherentes, regularisation des suites, applications. Paris: Gauthier-Villars 1952 11. Nelson,E.: Construction of quantum fields from Markoff fields. J. Funct. Anal. 12, 97 (1973) 12. Osterwalder,K., Schrader,R.: Axioms for Euclidean Green's functions. Commun. math. Phys. 31, 83 (1973) 13. Osterwalder,K.: Euclidean Green's functions and Wightman distributions. In: Velo,G., Wight-man, A. S. (Eds.): Constructive quantum field theory, Lecture notes in physics. Berlin-Heidelberg-New York: Springer 1973 14. Schwartz,L.: Theorie des distributions, p. 260. Paris: Hermann 1966 15. Simon, B.: Positivity of the Hamiltonian semigroup and the construction of Euclidean region fields. Helv. Phys. Acta 46, 686 (1973) 16. Simon, B.: Private communication 17. Simon, B.: Distributions and their hermite expansions. J. Math. Phys. 12, 140 (1971) 18. Stein,M., Weiss,G.: Fourier analysis on Euclidean spaces, p. 38. Princeton University Press 1971 19. Velo,G., Wightman,A.S. (Eds.): Constructive quantum field theory, Lecture notes in physics. Berlin-Heidelberg-New York: Springer 1973 20. Vladimirov,V. S.: Methods of the theory of functions of several complex variables. Cambridge and London: MIT Press 1966 21. Whitney,H.: Analytic extensions of dίfferentiable functions defined in closed sets. Trans. Amer. Math. Soc. 36, 63 (1934) Communicated by A. S. Wightman Konrad Osterwalder Jefferson Laboratory of Physics Harvard University Cambridge, Mass. 02138, USA Robert Schrader Institut fur Theoretische Physik Freie Universitat Berlin D-1000 Berlin
