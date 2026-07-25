Title: Download

URL Source: https://projecteuclid.org/download/pdf_1/euclid.cmp/1103858969

Number of Pages: 30

Markdown Content:
Commun. math. Phys. 31, 83-112 (1973) © by Springer-Verlag 1973 

# Axioms for Euclidean Green's Functions 

Konrad Osterwalder* and Robert Schrader** 

Lyman Laboratory of Physics, Harvard University, Cambridge, Mass. USA Received December 18, 1972 

Abstract. We establish necessary and sufficient conditions for Euclidean Green's functions to define a unique Wightman field theory. 

Contents 

1 Introduction 83 2. Test Functions and Distributions 85 3. The Axioms, Main Theorems 87 4. TheoremE->R 90 4.1. Construction of the Wightman Distributions 90 4.2. Lorentz Covariance and Spectrum Condition 94 4.3. Positivity 94 4.4. Cluster Property 96 4.5. Locality 97 5. Theorem R->E 97 6. Arbitrary Spinor Fields 102 7. Application 105 8. Technicalities . . 105 

1. Introduction 

In a relativislic quantum field theory the indefinite metric of Minkowski space causes many problems which could be avoided by replacing the time t by it or the energy E by iE, thereby passing from Minkowski space to Euclidean space. This idea was first used by Dyson [3] in perturbation theory. He continued the Feynman integrands analytically to imaginary energies in order to move the paths of integration away from the mass shell singularities of the causal propagators. Schwinger [21,22] studied the analytic continuation of time ordered 

* Supported by the National Science Foundation under grant GP31239X. ** Supported in part by the Air Force Office of Scientific Research, contract AF 44620-70-C-0030. 84 K. Osterwalder and R. Schrader: 

Green's functions to imaginary times and their transformation properties under the Euclidean group. He determined the Euclidean Green's functions (Schwinger functions) as solutions of certain differential equations. In axiomatic field theory it followed from investigations by Wightman [28], by Hall and Wightman [10] and by Jost [13] that the Green's functions (Wightman distributions) are boundary values of functions (Wightman functions) which are analytic in the permuted extended tubes. The Euclidean Green's functions could then be defined as the restriction of the Wightman functions to points with imaginary time and real space components [20, 24]. Symanzik [24, 25] advocated a purely Euclidean approach to quantum field theory: he realized, that given a formal Lagrangian density, the construction of Euclidean Green's functions might be simpler than the direct construction of Wightman distributions. Postponing the problem of continuing back to real time he studied the Euclidean Green's functions for models with boson self-interaction and established a useful connection to classical statistical mechanics. An abstract formulation was introduced by Nelson [15,17]. He described Euclidean boson quantum field theory as a Markoff process: the Euclidean fields are random variables and the Green's functions are expectations of products of random variables. Starting from a Euclidean Markoff field, which in addition satisfies certain regularity conditions, Nelson reconstructed a relativistic quantum field theory obeying the Wightman axioms. In this paper we give necessary and sufficient conditions under which Euclidean Green's functions have analytic continuations whose boundary values define a unique set of Wightman distributions. These conditions are (E0) Temperedness, (E1) Euclidean covariance, (E2) Positivity, (E3) Symmetry, (E 4) Cluster property. Surprisingly, Wightman's spectrum condition is a consequence of (E 0), (E1) and (E 2). Using (E 2) we construct a Hubert space X. By (E1) there exists a semigroup T\ t ^ 0 , on X, whose matrix elements by (EO) grow at most polynomially as t goes to infinity. Hence V is a contraction semigroup and V = e~ tH , where H^O. This gives the spectrum condition. Furthermore T\ R e τ ^ O , defines a holomorphic semigroup which we use to construct the analytic continuation of the Euclidean Green's functions and the Wightman distributions. All the Wightman axioms follow easily. The Hubert space X turns out to be the Hubert space of Wightman's reconstruction theorem. The following chart connecting Axioms for Euclidean Green's Functions 85 

the Euclidean axioms and the relativistic (Wightman) axioms gives the main theorem of this paper.        

> Euclidean Relativistic
> Temperedness Covariance Positivity Temperedness Covariance Positivity Spectrum [ ] + Symmetry <>[ J + Locality [ ] + Cluster <>[ ] + Cluster

Some of our methods have been inspired by Nelson's work [16]. Properties (El),(E3) and (E4) are obvious "continuations" of the Wightman axioms and have been known for a long time, [21,24]. Symanzik [25] has introduced a positivity condition which is different from (E2). His condition is necessary for the existence of Euclidean field operators. It is probably true only for a restricted class of models and does not necessarily allow a reconstruction of the Wightman theory. Our paper is organized as follows. In Chapter 2 we introduce some test function spaces and their duals. In Chapter 3 we formulate the axioms for Euclidean Green's functions and state our main theorems, which we prove in Chapters 4 and 5. Chapters 3-5 deal only with a single hermitean scalar field. The generalization to arbitrary spinor fields is given in Chapter 6. In Chapter 7 we make some remarks about possible applications of our results to constructive field theory. In Chapter 8 we give the proofs of some previously used technical lemmas. 

2. Test Functions and Distributions 

In this chapter we introduce some test function spaces and their dual spaces. They are all related to Schwartz's space 8P. 

We use the notation x for a point in 1R 4 whose coordinates in a fixed frame of reference are given by (x°, x 1, x 2, x 3) = (x°,x) We call the direction of e 0 = (1,0) "time direction", all directions orthogonal to 

> 3

e0 are "space directions". The scalar product x j ' = λ' o

y°— £ χk

yk

> k-=l

= x°}'° —xv; is always the Minkowski inner product. We also use the standard notation 

> D

## " =

## ( δ ί ? F ' ~ ( ^ r Γ

## ' w h e r e 

## «=(«. «2.•••«•-)' 86 K. Osterwalder and R. Schrader: 

ot k ^ 0, |α| = Σα k . For fe Sf OR 4") we define the ^-norm | / | m by 

## | / | m = sup |(l + |x| 2Γ/ 2/(α) fe, . ^)U 

> xteIR 4

where |x| 2 - £ (4) 2 and / ( α ) = D α /

> ί./c

Let °^(IR 4n ) be the space of test functions / e ^(IR 4 ") with the property that / ( x l 5 ... xn) together with all its partial derivatives /ί α ) (x 1 ? ... x π)vanish if x t = x ; for some 1 ^ / < / ^ n. °5^ (IR 4π ) equipped with the induced topology of y(lR 4 ") is a closed subspace of ,9 ?{R An ). We also define closed subspaces of °^(IR 4π ) by S?JlR* n)=={fe^(1R 4n )'J i*)(x ί,...x n) = () for all α unless s < xj < x° 2 < • • < x£ < ί}, all with the induced topology of i/flR 4"). We define «9ΌR + )C^(IR) to be the space of the functions with supp/clR + = [0, oo). By ^ ( I R 4 ) we denote the completed topologi-cal tensor product ^(!R + )(g)^(lR 3); i.e. /e^flR 4 ,) if / G ^ ( 1 R 4 ) and supp/c{x;x°^0}. We also define «^(IR_) = {/G^(IR);supρ/c{x:x^O}}. Finally we introduce the topological quotient space = ^(IR)/^(1R_), see e.g. [19], Chapter V. Let / be an element in y

then the equivalence class {/ + Sf (1R_)}, denoted by / + ? is an element in ^(1R)/^(1R_). We think of/+ as being the restriction /(x)|ΊR+ of f(x) 

to the right half line 1 R + . Because ^(IR) is a Frechet space and y(lR_) is a closed subspace, £f(JR + ) is again a Frechet space and thus complete, [19], Chapter VI, Proposition 13. The topology of y(IR + ) is given by the denumerable set of seminorms The seminorms (2.1) are not very convenient for actual calculations, but by Lemma 8.1 they can always be replaced by the equivalent set 

of seminorms , r .„ ίΛ ?χ m/ 9 , w w ,

| / + 1 ; = sup (1 + x 2

f/ 2 

|/(«)(χ)|. (2.2) The space < S^(1R + ) is isomorphic to the space of all functions defined on [0, oo) that are infinitely differentiable (right derivatives at x = 0) and of fast decrease at infinity, if we equip this space with the topology defined by the seminorms (2.2). Without danger of confusion we may simply identify this space with y(ΪR + ). An element in the dual space ^ /

(1R +) is a distribution in ^'(IR) with support in IR+ = [0, oo). We also define 

Sf$k\) as the completed topological tensor product Γ^(ΪR +)(§)^(1R 3

). An element /+ e ^ 0 R 4

) is thus the restriction of some / e ^ ( ΐ R 4

) to Axioms for Euclidean Green's Functions 87 

IR + xIR 3. Let 5^ be one of the lest function spaces introduced above. Then we denote by ® π ^ * the n fold completed topolojgical tensor product of ,9ς. We abbreviate ®nSfQR%) by ^flR 4"") and ®ny{jk\) by y(!Rt""). All the spaces introduced here are nuclear spaces, [5] I, §3.6. Thus e.g. any continuous bilinear functional T on £f(\R +) x5^0R 3)defines a unique distribution in ^'(IR 4), etc. We also introduce the spaces ^ , ^ + , ^ < and ίfOR 4.')- An element / in ^ ( ^ , ^ ( l f ) ) is a sequence/ - {/ 0,/i,/ 2? .••} wilh/ 0 e <C,/ πe^(lR 4π )(y +(1R 4π ),5^(Et'")),«= 1,2,..., and all but finitely_many / π's are equal torero. We equip the spaces £?,¥+,£?< and SfORt') with the direct sum topologies induced by the topologies of ^(1R 4"),^ +(1R 4"),^<(1R 4") and SfφX n) respectively, and we write ^ = 0 ^ ( 1 R 4 " ) , etc. These topologies have the property that a linear map t from 6f {¥ 

into a convex space J^ is continuous if and only if [t o /J is a continuous map from ^(1R 4") ψ> % (ΪR 4/ί ), «^(Kί"")) into #", for n = 0, 1, 2 .... We have denoted by ./„ the natural injection of ^(1R 4 M ) (^ + (lR 4 "),^(R 4 n )) into ^(^+,^(ΪRi)) See [19], Chapter V,§ 6, and also [1], appendix. On ^ we define involutions     

> / - / * by / * ( 2 ί i , . . . ^ ) = / Λ( ^ , . . . X i ) ,

and 

f-Θf by ( 0 / U x , . . . x , ) - / , ^ ! , . . . 5x n), where Sbc = ( —x°,x) and " means complex conjugation. Following [1] for/,0 6 5^, we define/ xge^ by 

> n

(/X£)π= Σ fn-k X9k-

> k = 0

In particular f o r / ^ 6 5^ +, we find that (Θf*) xg e ^ < . Finally we introduce some notational conventions. If / is in some space 5 ^ and T is in the dual space Sf'^ of 5 ^ then we use both T(f) 

and J T(x 1 ? ... x j / ( x 1 ? . . . x M) <^ 4n x to denote the value of T in /. Let fe ^(IR 4 "), JR e S 0 4 , α e 1R 4 and let π an element in Pn, the group of permutations of n objects (the letter 6 n will be used elsewhere). Then we define / (?>jR) and fπ by / ( 5 . Λ ) ( ^ l 5 . . . ^cj = /(Rx 1 + α , . . . jRx« + α), and / % i , . . . ^ J = / U π ( i ) , . . . ^ π( ,)) Also we define /+(x 1 ? ... x n) to be the restriction o f / ( x l 5 . . . xn) to the subset {x 1? ... x n ; x ? ^ 0 , . . . x ° ^ 0 } of 1R 4", and we sometimes write f+(x u... xn) a s / ( x l 5 . . . x Π)|"{x°^0}. 

3. The Axioms, Main Theorems 

In this chapter we formulate the axioms for the Euclidean Green's functions {S Π}. We also state our main theorems. 88 K. Osterwalder and R. Schrader: 

We shall assume that { S J ^ = 0 is a sequence of distributions Sπ (x 1 ? ... xn) with the following properties (n= 1,2,...): EO: Distributions     

> rx —1fee ^Cf"ίλQ^ n\

E 1: Euclidean Invariance 

E2: Positivity 

Σ SB+ m(θf* x / J £ 0, for all fe,? +. 

> n, m

E 3 : Symmetry 

®n(/)=Sn(/ π )> for all permutations π e P n , all /e°y(IR 4 / l ). E4: Cluster Property 

Km X {S n + m (Θ/ n * x ^ m ( ,0 , υ ) - $„(©/*) S m (0 m )} = 0 , for all j\geS/ +, Q = (0,a), aelR 3.For completeness we also list the axioms for the Wightman distributions {$B n}^o as they are given on p. 117 of [23]. The ΪB Π are supposed to be distributions with the properties R0: Temperedness, R 1 : Relativistic invariance, R2: Positivity, R 3 : Local commutativity, R4: Cluster property, R5: Spectral condition. We do not list hermiticity as an extra condition, because we do not have to make a distinction between linear and nonlinear conditions. The main results of this paper are the following theorems. 

Theorem E->R. To a given sequence of Euclidean Green's functions satisfying E0-Έ4, there corresponds a unique sequence of Wightman distributions with the properties R0—R5. 

Theorem R-^E. To a given sequence of Wightman distributions satisfying R 0 - R 5 , there corresponds a unique sequence of Euclidean Green's functions with the properties E 0—E 4. 

Remarks 

1. The choice of ^'(IR 4

") as distribution space for the S Π is natural because it makes the correspondence between { 6 J and {2BJ unique. Axioms for Euclidean Green's Functions 89 

Indeed, two sequences {6 „} and {SJ,} of Euclidean Green's functions with the properties that (£ n and <5' n are in y (lR 4n ) and that S M — SJ, has support in {x 1? ... xn;x t = Xj for some 1 ^ / < / ^ π}, lead to the same set of Wightman distributions. Equivalently we may say that the Wightman distributions tell us nothing about the Euclidean Green's functions in points of coinciding arguments. 2. Even if the properties (E2) and (E4) seem to depend on the choice of the "time direction" e0 in 1R 4, property (E1) shows that this dependence is only spurious and that (E 2) and (E 4) have to hold for any choice of 

e0. We have chosen the non covariant formulation (E4) of the cluster property only for convenience. Without any change in our results we could replace (E4) by the following covariant condition. E4': lim {S n + m ( / x ^ f l i l ) ) - S n ( / ) S m f e ) } = 0, (3.1)  

> λ-* oc

for all /e°y c (IR 4 w ), g e°// c(JR 4m ), geJR 4 .

(°y c(lR 4n ) is the set of all elements in °^(IR 4n ) with compact support). However there seems to be no covariant formulation of the positivity condition, because the "time inversion operator" Θ enters (E2) in a crucial way. We remark that exponential vanishing of the expression on the left hand side of (3.1) is equivalent with a mass gap in the relativistic theory, see Ref. [9]. 3. It follows from the proofs of our theorems that property (EO) could be replaced by the weaker - but non covariant - condition EO': 6 π e ^ < ( I R 4

" ) . This condition becomes important if we want to prove the equiv-alence of subsets of the axioms, in particular if these subsets do not contain symmetry (E3) and locality (R3) respectively. More precisely our theorems remain true if we replace {EO—E4|R0—R5} by either of (a) {EO',E1,E2|RO,R1,R2,R5}, (b) {EO-E3|RO-R3,R5}, (c) {EO', E1, E2, E 4 | R 0 , R1, R2, R4, R5}. (See also chart on p. 85). This follows from Chapters 4 and 5. 4. Obviously the translation scheme E<-»R may be extended to the case where the theory has additional symmetry properties. In particular the symmetries P, C and T of the relaίivistic theory can be expressed as symmetry properties of the Euclidean Green's functions. The symmetry property of the Euclidean Green's functions corresponding to PCT 

is an immediate consequence of axioms (El) and (E3). This is the well known PCT theorem. 90 K. Osterwalder and R. Schrader: 

4. Theorem E ^ R 

In this chapter we prove theorem E-»R. Given a sequence of Euclidean Green's functions satisfying (E0)-(E4) we construct explicitly a sequence of Wightman distributions satisfying (R0)-(R5). The main steps in this construction are the following: a) Using (E0) and (E2) we define a positive semi-definite form 

(f,β)= X &n +m {Θf* xg m) on &*+ x ^ + . After dividing out the vectors  

> n, m

of norm zero we obtain a pre Hubert space, whose completion we denote by X. 

b) By (E0) and (El) there exists a one parameter semigroup 

[T* = e~ tH }t>0 of self-adjoint contractions on jf, which can be extended to a holomorphic semigroup Tτ, Re τ ^ 0. With the help of this holo-morphic semigroup we show that the Euclidean Green's functions are the Fourier-Laplace transforms of distributions 2B W in 9?l which have certain support properties. We define 2B n, the Fourier transforms of 2B Π, to be the Wightman distributions. (R0) follows immediately. c) Euclidean invariance (E1) of (Zn now implies relativistic invariance (Rl) of 2B n, and the support properties of %B n give the spectrum condi-tion (R 5). d) Using positivity (E2) we prove positivity (R2), and we will show that the Hubert space Jf, constructed at the beginning, is the Hubert space of Wightman's reconstruction theorem. e) Using the cluster property (E4) we prove the cluster property (R4) and f) Using symmetry (E3) and a theorem in Ref. [12], p. 83, we show local commutativity (R3). 

4Λ. Construction of the Wightman Distributions 

Let {® n}^=o be a sequence of distributions satisfying conditions (E0)-(E4). As a preliminary step of our construction we use (E0) and the translation invariance (El) of S n to conclude that there exists a unique sequence of distributions Sn(ξ u ... ξn) in ^'(\RX' n) such that for 

## /( J ^ O 4

## )

In the sense of distributions this means 

> (

^n(^--^) = Sn_1(x 2-x 1,...x n-x n_1)ί for x?<x°< - <x°. (4.1) The distributions Sn are invariant under S0 4 in a restricted sense: 

## W1,...Ry^ fl κ1,...y, (4.2) 

provided ξ° k > 0 and (R ξk)° > 0, k = 1,... n. Axioms for Euclidean Green's Functions 91 

Now we define on <9% x 5^ + a sesquiiinear form by 

## (/•£)= Σ &n+ JΘf,?xg m). (4.3)  

> n, m

This form is positive semidefinite due to (E 2), it is linear in g, antilinear i n / and it satisfies (J,β) = (β,f), for all]\βeSf+. Denoting by Jί the set of vectors in 5^ + of norm zero, Jί = {/e 5^ + | | / 1 | 2 = (/,/) = 0}, we define X to be the Hubert space completion of the quotient space 5^ +//K By v we denote the canonical injection of ξ£ '+ into X. Then for 

^- E ~+' (v(fl ^9))yr = (/>£) > (4.4) and the range of i;, denoted by ^ 0 is a dense subset of jf". By (E0), ι? is a continuous map from 5^ + onto ® 0 .and α = fθ,α), we define t/ s (α)/by 

( ) fe - XJ = fn(Xi -Qτ> %n ~ Q) • 

and Thus extension of (4.5) 

by continuity leads to a unitary representation Us(a) in X of the three dimensional translation group (translations in space directions). For translations in the time direction the situation is different because the sesquiiinear form (4.3) and hence the scalar product in X

involves a time inversion Θ. For ί^O we define the map T r

from ^ +

into itself by ( Γ / ) ( & , . . . xn) = f n(x i-t,...x n-t), (4.6) where ί = (ί,0). By (El) and definition (4.3), for/,_g,e sS? + and ί^O, 

(ir β) = (f%g). (4.7) 

Furthermore for s,ί^0we have 

By (4.1), we find that for/e ^ + ,

## K/ 7"7)I = | Σ ί/«ί^ n ,... %,)/ M ί>Ί,... y j  

> I n , m 92 K. Osterwalder and R. Schrader:

for some polynomial P(ί), which depends o n / . This follows from the facts that Sm+n ^1 is in Sf'(1R% im f / l ~ υ ) , and t h a t / h a s only a finite number of nonvanishing components. We can improve inequality (4.8) by arepeated application of the Schwarz inequality and of (4.7) and (4.8). 

## -° 2

## (Λf 2

## "'/) 2

for all ft = 1, 2,... Taking the limit as n-+oo we obtain 

## 1| 2

## . (4.9) 

It follows from (4.9) that V maps one equivalence class mod Λr onto another equivalence class mod j\ r . Thus for t ^ 0 defines a continuous one paremater semigroup {To} f>o of operators on SJ 0 C Jf and TQ is positive, symmetric and has norm smaller or equal to one. Therefore TQ has a self-adjoint extension, denoted by T\ 

and {T t}t>Q is a weakly continuous one parameter semigroup of self-adjoint contractions on X. Let H be the infinitesimal generator of V. 

It is a positive self-adjoint operator on j f and we can define the one parameter group of unitary operators γιs = e ιsH , — oo < s < oo. This is the unitary representation of the time translation group and we set         

> U(a) =Tίa °Us(a) ,a = (a 0,a) e 1R 4.

This defines a unitary representation of the four dimensional translation group in JΓ. The family Tτ

=VT ι

\τ = t + is, is a holomorphic semigroup for Reτ = f > 0 , uniformly bounded and strongly continuous for R e τ ^ O . We can use this holomorphic semigroup to construct the analytic continuation of the Euclidean Green's functions. L e t / w = (0, ...,/ w ,0 ...) and_g = (O,...,0 π,O ...) be vectors i n ^ V Then / m 6 ^ + ( l R 4 m 

) , ^ G ^ + ( I R 4 π 

) and Θf* xg ne^(]R 4{m + n) 

). Thus for ί ^ O fixed and h e Sf (1R), the mapping 

(Θf* xg n,h)-+S(υ(f m), Tΐ + ίs 

v(g n)) y,h(s)ds (4.10) defines a continuous linear functional on ^<(]R 4(m + n) 

)%)S/ ?

(]R), by the nuclear theorem. Moreover, for any a e 1R 3

, α° ^ 0, Axioms for Euclidean Green's Functions 93 

We conclude that the right hand side of (4.10) can be written as 

s)ds ^gjy,, ... yjh(s) (4.11) where S^ nlm^1(ξ 1,... ξm + n -1 \s) is a distribution in the dual space of 

<cf(]RX (m + π "l) )(χ), (/(lR) and a continuous function of s when smeared in all the other variables. Furthermore Now let M ^ i - Cm-i. ίm, C m + i, ... $m + n -i) b e a n element in y ^ ' ^ ^ ^ ^ J R ^ y ί l R 4 ^ " " 1 1 ) and set for ί > 0 

# s( m ) (t = < £ , s | U = J s ! ^ 

It follows from (4.11) that for fixed hm, S(m) (ί, s|/i m) is a distribution in the dual space of t9ί7 (lR + )® ty7(lR) and satisfies the Cauchy-Rie-mann equation for ΐ > 0, — GO < s < GO. Hence by Lemma 8.7 there is a distribution S{m) {a\h m) in ^'(ΠL) such that S(m) is the Fourier-Laplace transform of S{m) . S{m) (t, s\h m)= \ e~* {t + is) Sim) {a\h m)da, and ^ + π - i ( ί i . • •• (t, ξml ••• ξ m + n-i\s) i s t h e analytic continuation of 

Sm^. n_ί(ξ u... (t,ξ m\ ... ξ m + Λ _i) in the time component of the m-th variable. Lemma 8.8 shows that under these circumstances we can analytically continue Sm + n _ι simultaneously in the time components of all variables and that there exists a uniquely determined distribution 

Wn(q u ... qn) in </"&%'") such that    

> -Σ(ξkVk - Hkgk) „

Sn(ξ u... ξn) = \e — " " Wn(q u... qn)d*»q. (4.12) Now we define the Wightman distributions %B n by 

Wn(x u...x n) = je l

^ i i k + ί

*k) 

*k

Wn_ί(q l9 ...q n_1)d« n

-l) 

q. (4.13) According to the results of Chapter 2, [see the discussion following Eq.(2.2)] Wn(q ί9 ... qn) is a distribution in ^'(IR 4

") with support in {</!,... g n ; ^ ? ^ 0 , . . . 4π^0}. In Section4.2 we prove that for ΛeV +,Wn{Λq x, ... Λq n)= Wn(q 1, ... qn). Hence the support of Wn is in 

{q x,... qn:q 1eV +,... qneV +}, where V+ is the forward light cone. This is the spectrum condition (R5). Temperedness (RO) follows from (4.13). 94 K. Osterwalder and R. Schrader: 

4.2. Lorentz Coυariance and Spectrum Condition 

Translation invariance of 2B n (x l 5 ... xn) follows from definition (4.13). Thus relativistic invariance (R 1) and also the spectrum condition (R5) follow if we can prove that for all A e L\ ,or equivalenlly if we can prove that for 0 ^ i <j ^ 3, 

XιJ Wn(q 1,...q n) = 0, (4.14) where Xtj are the operators From Eq. (4.2) we conclude that for 0 g i <j ^ 3, y , J . S B ( | I , . . . g = 0, (4.15) where 

v = y (piJ--£jJ I ι j LJ ^k Ά y j ^ k 7\. 

On the other hand we get from Eq. (4.12)   

> -Σi&qί-iξkqk)

Yιj Sn(ξ ί,...ξJ = je - 1

"• XlJ Wn(q u...q n)d* n

q, (4.16) 

for 1 ^ i < j ^ 3, and   

> -Σ(&qk-iξkqk)

YOj Sn(ξu .ξJ = ίίe - i •• XOj Wn(< lί9 ...q n)d* n

q, (4.17) 

for j = 1,2, 3. [To prove Eq. (4.16) we use the definitions of the Fourier transform and of the derivative of a distribution; to prove (4.17) we also need Lemma 8.4.] Eq. (4.14) is now a consequence of Eqs. (4.15-17) and of the uniqueness theorem for Laplace and Fourier transforms of distributions. 

4.3. Positivity 

In this section we prove the positivity condition (R2). We have to show that for all fe ££ 

## ΣW Jf*fJ (418) Axioms for Euclidean Green's Functions 95 

is nonnegalive. The idea of the proof is simple. We show that any element / e ^ defines a vector u(f) in the Hubert space jf, constructed in Section 4.1, and that the norm of u(f) is given by (4.18). We also show that the set ζd x = {u(f);feS?} is dense in jf. Hence X is the Hubert space of Wightman's reconstruction theorem. For fe &>+ (lR 4n 

) we define p e 9>^% n

) by Then for/e5^+ we define/by Λ(gi,.. ? J = i / « % , . . . U e ^ ^ l

"k

~k) 

d*»ξ\{q ok^O}. (4.20) 

Lemma 4.1. The map f-+f for f e^ + is a continuous map of ,9" +

onto a dense subset ££ of 5^(IR 4

'). The kernel of this map is {0}. 

Proof. It suffices to show that for n = 1,2, ...,/„-•/„ is a continuous map of f^VflR 4n 

) onto a dense subset ^(IR 4 1 1 

) of .^flR 4

/") and that the kernel of this map is {0}. The map / n ^ / J , defined by (4.19) is an iso-morphism of 6? + (IR 4

") onto £f (1R 4

/"), therefore the lemma follows if we can prove that / J - > / π is a continuous map of 5^OR 4

,'") onto a dense subset 

y+(R 4n 

) of ^(ΪRt'") wίώ kernel {0}. But this is an easy consequence of Lemma 8.2 and the fact that the Fourier transform is a homomorphism ofί^IR) onto itself. In Section 4.1 we have introduced a continuous map v from 5^ +

onto a dense subset ^ 0 of Jf. By Lemma 4.1, the map w defined by 

M'f) = v(f), for fe¥ +, (4.21) 

is a map from the dense subset 5^ + of 5^(1R 4') onto S) 0C^ί. We want to show that w can be extended to a continuous map w from all of  

> 4

) onto a dense subset ® A of JΓ. This follows from 

Lemma 4.2. T/ie map w is continuous. Proof. Lelf,β e ¥ +. Then, by (4.21) and by (4.3), 

(4-22) 

We rewrite the last expression of (4.22) in terms of fn and gm. By (4.1) and (4.12) we find that this expression equals 

Σ lϊUBx,,, -9ξ n-u ..., - H J y t t L + ^ ξ n + i , - L+m - i ) (4-23)    

> Σ(ξkqi -ίξuqk) ^96 K. Osterwalder and R. Schrader:

Interchanging the order of integration in (4.23) we obtain 

> m-l)

(4.24) 

For the space components ξ\' 2

'3

and ql' 2

"3

the change in the order of integration is justified by the definition of the Fourier transform of a distribution. For the time components ς° and q% we refer to Lemma 8.4. By Lemma 4.1, / , and gm are elements in ^(ΪR 4

/' 7

) and ^(WX' m

)

respectively, and thus fn(q n,... qjgjq,,,... qn + m -ι) is in ymt' in + m

'l) 

y

On the other hand P^ I+ m _ 1 is a distribution in y /

( S f ( Λ + m 

~ 1 ) 

) . This proves Lemma 4.2. From Eq. (4.24) we conclude that for any h,ke ^(ΪR+') (w®, w(k))χ (4.25) Now let / e ££ a n d define / by {f) n = f n and   

> - i ΣqkCk

where fl is defined as in (4.19). Obviously /„ is the restriction to {q% ^ 0} of a test function in 6^(]R 4n 

) and is therefore an element in ,^(1R 4

") Furthermore the set {/ / G ^ 7

} is equal to 5^(ίR 4

). Therefore we may define a map u : !£ -> 3C by / -> u(f) = Mf) G Jf . (4.27) The range of u is &1 {= range of w), which is a dense subset of <if. 

Substituting (4.13) and (4.26) in (4.18) we find that f o r / e ^ , = Σ I / A , , . - . ^ ) / m ( ? , P • •• qn + m -ι) ^ B + m - i ( ? i . • •• 17,, + m 

/ / - («(/), «(/)),,., (4.28) where the second Eq. in (4.28) follows from (4.25). From Eq. (4.28) we now get the positivity condition (R2). The density of Q) γ in Jf implies that Jf is the Hubert space of Wightman's reconstruction theorem [23]. 

4.4. Cluster Property 

In this section we derive the cluster property (R4) from the cluster property (E4). Using (4.22) we rewrite (E4) in vector notation: lim (vv(/), Us(λa) w(β)) x = (vv(/), Ω)* (Ω, w(g))^ , (4.29) Axioms for Euclidean Green's Functions 97 

for / , g e ^ + . The vacuum vector Ω is defined to be ι;({ 1,0,0,...}). By continuity (4.29) remains true if we replace w{f) and w{g) by arbitrary vectors in jf, in particular we find that for all h,ke £f 

lim (u{hl U &(λa) u(k))# = (M(Λ), Ω)^ (Ω, u(k))χ-. (4.30)  

> Λ-> 00

Eq. (4.30) is the cluster property (R4) in vector notation. 

4.5. Locality 

For Re2^=0, Imz fc = 0 and z f c - z f e , φ 0 , if fcφk', we define the Wightman function by Then 3B M(z 1 ... zn) is symmetric in its arguments and has an V+ invariant, single valued, symmetric analytic continuation into the domain $ n = { z l 5 . . . zn\(z π(k) - zn{k _l) )e%k = 1,... n, for some permutation π(l),... π(ή) of 1,... n}. X is the forward tube {z I m z e V+}. This follows easily from the symmetry property (E2) for the Euclidean Green's functions and Eqs. (4.1), (4.12) and (4.14). Using the Bargmann Hall Wightman theorem, [10], we conclude that Wβ n{z i,... zfI ) allows even a single valued, symmetric L + ((C) invariant analytic continuation into the domain S^ = (J AS tr Now we use a theorem in Ref. [12] (p. 83,  

> AeL +(<C)

second theorem) to conclude that the boundary distributions 2B n(x l5 ... xn)

of %β n(z u ... zn) satisfy the locality condition (R3). 

5. Theorem R ^ E 

In this chapter we start from a relativistic field theory given by a sequence {2B n}£=o °f Wightman distributions, satisfying axioms (R0)-(R5), and we construct a sequence {S,,}^ =0 of Euclidean Green's functions with the properties (E0)—(E4). It is well known that the Wightman distribution sIB n is the boundary value of the Wightman function Wn(z 1, ...,z,,) which is analytic, single valued, symmetric and /L + (C) invariant for (z λ,..., zn)e Sζ, see [12], p. 83. S^ contains the set 

^° = {(z ls ... ztt ):lm(z k-z k_ί)eV + for all i<k^ή\, 

and it is invariant under permutations of ( z l 9 . . . zn). Hence it contains the set Sn = {(z, ,... zn): Re z° k = 0, lmz k = 0, zk Φ zw for all 1 ^ k < k' ^ ή). 

Points in Sn are called Euclidean points. The restriction of the Wightman 98 K Osterwalder and R. Schrader: 

functions to Euclidean points defines the Euclidean Green's functions. We set 6 0 = 2B 0 = 1 and for (x x,... xn) e Ωn = {x x ... xn xf Φ x 7 for all 1 ^ i </' ^ w}. The ® π, n = 0,1,..., are the Euclidean Green's functions and we have to verify that they have the properties (E0)-(E4). By (5.1), S π (x 1 ? ... xn)

is an analytic function, invariant under permutations of the arguments x l 9 . . . xn, which is (E3). It is invariant under translations, because 2B M

is. It is furthermore invariant under the action of the subgroup of those elements in L+((C) which map Euclidean points in Euclidean points. But this subgroup of L+ ((C) is just the group of Euclidean rotations. This proves (E1). Now we prove (E0). Obviously the linear space °^ C(IR 4") of all func-tions in 5^0R 4") with compact support in Ωn is dense in °^(1R 4"), and ®π (x 1 ? ... xΛ) is a continuous, uniformly bounded function on any compact subset of Ωn. Hence the Riemannian integral 

Sn(f)=\S n(x 1,...x n)f(x ι,...x n)d 4n x (5.2) 

defines a linear functional on °5^(1R 4"), which is symmetric under permuta-tions of the arguments xx,... xn and invariant under iSO A. (Note that (x 1 ? ... xn)->(Rx 1 + g, ... Rx n + g\ ReSO^, αelR 4 , maps a compact set K in Ωn onto another compact set K1 in Ωn.) 

Proposition 5.1. For n— 1,2,..., there exists a constant c and a number m such that for all /e°^ c (lR 4 ") 

l® Λ (/)l^c|/| m . (5.3) 

Postponing the proof of the proposition, we use it together with the density of V c(lR 4n ) in V(IR 4 n ) to extend ® M to a distribution in ^ ( I R 4 " ) , proving (E0). By continuity this distribution, again denoted by ® M, has the in variance property (E1) and the symmetry property (E3). Positivity (E2) follows from the arguments given in Section 4.3. Let fe^ +. Then according to (4.22) and (4.24) 

> n,m

Axiom (R2) implies that (5.4) is nonnegative because f o r / e ^ V , /„ is in ^(IR 4

^^ and can therefore be interpreted as the restriction to {q% ^0} of some function gn(q l9 ... qt) in ^(1R 4

"). The cluster property (E4) follows from (R4) by the arguments of Section 4.4: (R4) implies that Axioms for Euclidean Green's Functions 99 

lim UF, U s(λa) G) - (F, Ω) (Ω, G)] = 0 for all F , G e / , and this 

> Λ-»oo

implies (E4). Now we return to Proposition 5.1. Its proof has a geometrical and an analytical part. Let us do geometry first. 

Lemma 5.2. For n = 2, 3,... there exist N = N(n) < oo unit vectors el9 ... e N in IR 4 and a constant Λ>0, depending on n, such that for all (x u...x n)eΩ n

## i | < > l t e ) 1 (55 | < & 5 f > l   

> ki< j

where <, > is the Euclidean scalar product, and 

(

Proof. Pick N > 3 2~ ι n(n — 1) vectors e1,... £N such that any four of them span IR 4. Now take ( x l 5 . . . xn) e Ω n and define 2~ ίn(n—l) unit vectors Then each of the vectors ftj is orthogonal to at most 3 vectors er, e s, e t,

and because of the choice of JV, <e M , / 0 > φ 0 for at least one M e {1,2,... N} and all / i j r i.e. h ( / ) = m a x m i n | < e f c , / i j > | > 0 for all / = {/ 12 ,... / B .l B } . As ( x l 5 . . . xn) varies over Ωm f varies over the 2~ 1n(n— 1) fold tensor product of the unit sphere in IR 4

, which is a compact set, and we have 

h(f)>0. Thus there is a constant A>0 such that h(f)^A, for all /, i.e. for all (x 1 ? ... x j e β π

max mm  

> kίj

Using the inequality ρ(x Λ ... x n)^\x i — x^ 1 for all l^i<j^n, we prove (5.5). We choose N unit vectors as in Lemma 5.3. These vectors remain fixed for the remainder of the proof. Then we define N n! open subsets 

Ωfcπ ={(x 1,... xn):<e k,x πU+1) -x πU) )>0 for all i^j<n}, 

where π is an element in the permutation group Pn of n elements and 

k=l,... N. The Ωkπ obviously cover Ωn.

For the analytic part of the proof of Proposition 5.1 we have to define a partition of unity on Ωn: Let τe C°°(1R) be such that Orgτrg 1 100 K. Osterwalder and R. Schrader: 

and τ(x) = 0 for x<j\ τ(x)=l, for x ^ l . Then we define χ f e π ^0 on β-by Zk«(^l,. *n) = Π T ( X - ^ ( X 1 5 . . . XnXgfc^πO + D - ί π O )))* where A is as in (5.5). Obviously suppχ kπ c Ωkπ . From Lemma 5.2 we now conclude that for any (x 1 ? ... x j e Ω w there exists fc, π such that Z**(*i .••&,)= 1, a n d therefore Σ Xkn(Xl>' ^ J ^ 1

> fe,π

on Ωn. Now we can define and χkπ is well defined and nonnegative on Ωn\ Σ Z/cπ = 1 o n ^« 5 i e Zfcπ 

> k,n

defines a partition of unity on Ωn. For /e°^(IR 4 n ) we can now write £„(/)= Σ ^ ( χ k π / ) , (5.7) 

> k,π

and for a proof of Proposition 5.1 it suffices to estimate a single term in the sum on the right hand side of (5.7). Using (5.2), and the symmetry and S0 4 in variance of S n we write 

(χ kj)=^(x ux)(χ kf)(x 1...x n)d 4n x

where π' is the inverse permutation of π and R e S 0 4 is chosen such that jR" x

ek is the unit vector in the time direction, i.e. R~ 1

ek = (l,0). As χkπ 

has its support in Ωkπ , (χ kπ f)*o R) has its support in Ω < = {x l J ... xn;

x ? + 1 - x ? > 0 , 7 = 1 , . . . n - l } 5 and is therefore in ^<(!R 4 n 

)n^ c (lR 4 n 

). To finish the proof of Proposition 5.1 we need two more lemmas L e m m a 5.3. The restriction of ® n ( x i , • •• x«) to Ω< defines a distribu-tion in ^ ( I R 4

" ) . Lemma 5.4. For α// m x ^ 0 there exist constants c and m depending only on ml 5 such that \lkπf\my< C

\f\m> forallk=l,... N, 

We use Lemma 5.3 to show that there exist constants c and m1 such that (using 5.8) 

\&n(XkJ)\=\&n((Xknf)?O, R) )\ Sc\(χ kπ f%, R) \mχ = c\χ kπ f\ mi ,

and Proposition 5.1 follows from (5.7), (5.9) and Lemma 5.4. Axioms for Euclidean Green's Functions 101 

Proof of Lemma 53: For (x 1 ? ... xn)eΩ < we can write   

> -Σ(ξ

where ξ k = x k + i —x fc and ξ ? > 0 for ( x l 9 . . . i J e Ω < . It suffices to prove that S W Ί!(£!,... ^ _ i ) is in y'(IR+"). By the nuclear theorem and the support properties of Wn_ι{q 1,... qn-ι) we only need to show that for 

W(q) e «?"flR + ) and gξ(q) = e' ξq (q ;> 0), the function S{ξ) = P^^^) f (ξ > 0) defines a distribution in .5^ /

flR + ). But for £ > 0 

dq« 

for some constants c{ and m. Now let / e ^ ( I R + ). Because /(x) vanishes together with all its derivatives /(α) (x) at x = 0, we can write it as 

x

f(x)= —rf (n) (y x) for any n^O and some yx, 0^y x^x. Then we find 

that for some constants c, 

\f{ξ)W{g ξ)dξ of i m ) 

(Jcj sup {(l \f(ξ)\} + sup  

> 0m I

This proves the assertion and thus Lemma 5.3. 

Proof of Lemma 5.4. We use the following estimates on derivatives             

> lv ( α ) ίΎ Y)\<ΓΠ(Y T \l αll A k π V ^ l ϊ xn ) \ = Ca Q \ £ l i ••• ^ n i < / yi γ . _ γ ι-ι*ι

Then the lemma follows from arguments similar to those given at the end of the proof of Lemma 5.3. 102 K. Osterwalder and R. Schrader: 

6. Arbitrary Spinor Fields 

In this chapter we generalize the axioms (E0)-(E4) to include arbitrary spinor fields. We also show how to modify the arguments of Chapters 4 and 5 to prove theorems E->R and R->E in this general situation. The Wightman distributions are given by Here ψ^ z) (Xj) stands for one of the finite number of fields that describe the theory. v t represents a set of dotted and undotted indices ( α 1 ; . . . amk ,

β\-> ••• βnk ) a n d describes the spinor character of the field labeled by kt.

Finally v stands for the set v 1 ? ... vn and k stands for the set fc 1? ... kn.

Let S(A y B) be a finite dimensional analytic representation of 

SL{2X) x SL(2, 0, the universal covering group of L+(C). Then S(^4, ,4) is a representation of SL(2, (C), the universal covering group of 

V+, and all finite dimensional continuous representations of SL(2, <C) may be obtained in this way. The transformation properties of the fields are given by 

U{{g, A}) ψ ikι) (x) U({g, A})~ * = £ S ( k ι ) U " S Λ~^ψ Άa e 1R 4, ^1 e SL(2, C). (7 is a unitary representation of the inhomogeneous »SL(2,(C) and Sikι) (A, B) is a finite dimensional analytic representation of SL(2,(C)xSL(2,C). Furthermore Λ04,5) is given by A(AJΪ)z=AzB τ

> 3

where z = ^ zμσμ and z e (C 4. For notational convenience we denote 

> μ = 0

the adjoint fields ψ^ixf by ψ[* kι) (x\ where vf = (β x,... ^ ά l 9 . . . ά m k ). We have to require that S(kι) (A, B) vμ\ = S i~kι) {A,B) vJt. Relativistic co-variance leads to 

(Rl) ΏS vk (x ι,...χ n)=ΣS k(A-\A-1rvWμk (Λx γ + a,...Λx» + a), 

> β

for all AeSL(2Xl αelR 4 Here A=Λ(A,A) and Sk(A,B) is a finite dimensional analytic representation of SL(2, C) x 5L(2, <C). Again using formula (5.1) to define the Euclidean Green's function we find that the covariance axiom (E1) becomes (El) ® v f c ( ^ , . . . χJ=Σ S

k(V-1

,V-1

y;<5 μk (Rx 1 + Q,...Rχ n + q), 

for all U,VeSU(2\ gelR 4

. Here R = R{U,V) is defined by 

A(U,V)(-ix o

,x) = (-i(Rx)°,Rx) and is a homomorphism of Sl/(2) x S U(2) onto S 0 4 . Note that S (7(2) x S U(2) is the universal covering group of S0 4. Hence Sk(U 9 V) defines a continuous finite dimensional Axioms for Euclidean Green's Functions 103 

(one or two valued) representation of S0 4. Axiom (E0) remains of course unchanged and its derivation from the Wightman axioms is as in Chapter 5. Axiom (E3) becomes                          

> \CJ) wvJc^1?. . . xn)=σ ^ fc^ Λ π(1),. . . Λπ(Π) j

for all permutations π. Here σ = + 1 and v —(v π ( 1 ) ,... vπ(n) ), k = (fc π(1)5 ... k π(n) ), [14]. A reformulation of the nonlinear axioms (E2) and (E4) requires some modifications of the notation introduced in Chapter 2. In the following 5^+ will denote the set of all finite sequences / = (/o»/i>/2> • ••) where / o e C and each /„ is a sequence of elements 

fn,vk G ^+(lR 4n X with vk as before. Also for Je^ + we redefine f* by 

( f*\ (x x \— 7 (γ γ \ (fi 7\           

> \J )n, v/cV 5 l ' •••X
> n) ~ J n. v*k*\ X
> iv ••x
> l) •> l ° Z
> J

where v* = (v*,... vf) and k* = ( —k Π,... — k j . Furthermore for gelR 4

we define / ( ? ) by The remaining axioms can now be written as (E2) £ SvμU (Θ(f*) ntVk xf mttι ^0, forall / e ^ + . 

> M, m
> vk

(E4) lim X {S V ί l 

> n, m vk

forall f,g e £f +, α = (0,α), α e IR 3.(E2) and (E4) follow from the Wightman axioms as in Chapter 5. To reconstruct the Wightman distributions from a set of Euclidean Green's functions obeying (E0)-(E4) we proceed as in Chapter 4. The only step which has to be modified is the derivation of Lorentz co-variance of 2B vfc from Euclidean covariance of 6 v k . Given the Euclidean covariance of Svk (ξ 1,... ξn_1)= S v k ( x 1 ? . . . xn), ί, = xi +1 — xn ξ® > 0 , we have to prove the Lorentz covariance of Wvk (q γ,... qn), where S v k ( ξ l 5 . . . ξn)=$e *^ qiC l

"k

-k) 

Wvk (q u... qn)d* n

q. (6.3) First we note that any element A in SL(2,C) can be written as A = UH, 

where U e S 1/(2) and H is positive. Hence it is sufficient to prove that 

Wγk (q s,...qJ=Y jSk(U,UT vWμk (Λ-1

(U,U)q ί,...Λ-1

(U,U)qJ, (6.4) 

and 

, (6.5) 104 K. Oslerwalder and R. Schrader: 

for all UeSU{2) and all positive H. Eq. (6.4) follows immediately from (6.3) and (El) with V replaced by (7, because Λ(U, U) leaves the zero component invariant. To prove Eq. (6.5) we consider the one parameter group H(φ) = C o s h — -f Sinh — -e σ of hermitian operators, where e

is a fixed unit vector in R 3 and — oo <ψ < oo. Then it suffices to show that for Λ(φ) = Λ(H(φ), H(φ)\ the expression 

dφ 7

> μ
> *,β

\ dΨ d dφ 

vanishes. dφ Wμk (qi ,...q n) (6.6) Let V(φ) = cos — + / sin —- e-σ be a one parameter group in S (7(2) with e fixed, as above. Then Euclidean covariance of Svk implies that for  

> =y

ίdK 

## 7\ ^ , B) μy + BS k

dφ 

## Wli— P 

•U,^)ϊ From the definition of H(φ) and K(φ) we get (6.7) 

dH n

and Furthermore 

# Σ

dφ dV naβ 

dH r

(6.Ϊ 

> aβ

dφ — i= i(es) ,β •

and 

# Σ

dφ dq*  

> 1

ζif <5

dφ 3ξ? r I dξ{ 

(6.9)  

> 1 ^ J ^ 3 Axioms for Euclidean Green's Functions 105

Now we insert (6.8) and (6.9) in (6.6) and (6.7) respectively. Then the vanishing of (6.6) follows from (6.3) and (6.7) by the arguments of Section 3. 

7. Application 

By theorem E—>R, a relativistic quantum field theory model can be obtained by constructing a set of Euclidean Green's functions, satisfying (E0)-(E4). Formally the Euclidean Green's functions are given by where ΩE is the Euclidean no particle state, Aι(x^) are free Euclidean fields and V is the Euclidean action, [21] and [18]. By introducing a volume cutoff h and an ultraviolet cutoff κ we make S n > h > κ well defined objects. We define S n as the limit of S n h>κ as κ->oo, and /I->1. To complete the program we would have to show that this limit exists and has properties (E0)-(E4). Euclidean covariance (El) follows once the uniqueness of the limit is established. All the other axioms are expected to hold for the cutoff Green's functions, independently of κ and h. 

Estimates are needed to prove this assertion for (EO) (distribution property) and (E4) (cluster property). For superrenormalizable models the necessary techniques have been developed by Glimm and Jaffe [7, 8] and by Dimock, Glimm and Spencer [9, 2]. On the other hand, for models involving boson-fermion interactions, (E2) (symmetry) and (E3) (positivity) are trivially satisfied for a large class of cutoffs. The symmetry property follows from the fact that free Euclidean bose and fermi fields commute, respectively anticommute, with or without ultraviolet cutoff. If there is no ultraviolet cutoff in time direction then positivity (E3) follows from the Feynman-Kac formula and the relation connecting the Euclidean action V with its adjoint, [18]. 

8. Technicalities 

In this chapter we state and - where necessary - prove some technical lemmas, used in earlier chapters. 

Lemma 8.1. (see p. 86). The set of seminorms on 

m = l , 2 , . . . is equivalent to the set of seminorms \f+\' m

Proof. Obviously for /

\106 K. Osterwalder and R. Schrader: 

Thus it remains to prove that for a given m we can find c and n such that forall/e^flR), 'm^c\f +ζ. (8.1) Let ^{m) 

(R-) be the closure of y(1R_) with respect to the | |m-norm. Then | / + L = ^ ( m f ( R \f + g\ m. (8.2) Let φ(x) be a C 00 function such that 0 ^ φ(x) ^ 1, φ(x) = 0 for x :g — 1, 

φ(x) = 1 for x ^ — ^. Now we define     

> —— / ( x ) , /<9Γ X ^ 0 ,

10, /or x > 0 . Certainly g e Sf {m+ 1} (1R_), and  

> m + 1 ^.α

^ C l sup (8.3) for some constants cx. and c, depending on φ and m but not on /. Ineq. (8.1) follows from (8.2) and (8.3). Our proof of (8.3) is an adapted version of Hormanders proof of Whitney's extension theorem see [27] and [11]. 

Lemma 8.2. Suppose g(x) e ^flR+) and define g by Then ge5f(lR +) and g-^g is a continuous map of ^0R+) onto a dense subset S? of «9*(ίR + ). The kernel of this map is {0}. 

Proof. The integral [ e~ qx g(x) dx is uniformly convergent for q ^ 0, / d \m

ihus (I+ q) mD*g(q)= \e~ qx 1+ - — ((-x) ag(x))dx \ {q^O}. In par-\ dx I 

ticular (see (2.2)) Axioms for Euclidean Green's Functions 107 

for some constants c1 and c2. Ineq. (8.4) proves that g e yflR+) and that the map g-+g is continuous. In order to prove that the range £f of this map is dense in &?

(1R +) we take a distribution We£f'(lR +) with the property that W(g) = 0_ϊov all ge^(]R +) and show that this implies 

W = 0. As W is in &"(&+) it is a distribution in 5^(IR) with support in [0, oo) and its Fourier-Laplace transform \ e ιzq W(q)dq=W{z) is an analytic function in { z : I m z > 0 } . Now we need the following well known lemma. 

Lemma 8.3 ([26], p. 23). Suppose We&"(lR) and suppWc [0, oo). 

Then W= Σ D*μ Λ9 (8.5) 

where μα(g) are measures of power increase with support in [0, oo). 

Remark. We say a measure μ is of power increase of order a if J |dμ(x)| (1 + |x|)~ α < oo for some α ^ 0. Using (8.5) and the definition of ^ we now can write for ge 6f(JR +)

> W

(9)= Σ S($e-« xx*g(x)dx)dμ Λ(q) (8-6) We claim that ί ( ί | e - ^ x α ^ ( x ) | d x ) | d μ α ( ^ ) | < o o , (8.7) thus by Fubini's theorem we can change the order of integration in (8.6) and obtain 

## = Σ i(ϊe-* x

## D*dμ a(q))g(x)dx 

## l= M

## ° (8.8) 

- J W(ix)g(x)dx, 

> o

and we suppose (8.8) to vanish for all ge6^(lR +). As W(ix) is a real analytic function of x > 0, (8.8) implies that W(ix) = 0 for x > 0 and hence 

W(z) — 0 for Imz > 0. By the uniqueness of the Laplace-Fourier transform we conclude that the distribution W is identically zero, which proves the density of £f in ^(IR + ). The last statement of the lemma is obvious. It remains to prove Ineq. (8.7). Suppose μ α is of increase of order β > 0 . Then 

j{\e-« x\x*g(x)\dx)\dμ a(q)\ ^ sup((l + qf f e-* x

\x* g(x)\ dx) f \dμ a(q)\ d

\x*g(x)\dx (8.9) 108 K. Osterwalder and R. Schrader: 

for some constants cv, γ. Hence it suffices to show that sup \x k

g(x)\ 

is finite for any integer k. For nonnegative k this is trivial as g e 

For negative k we use the fact that g(x) vanishes with all its derivatives 

x~ k

x

at x = 0 and can be written as g(x) = -—— g{ k+1) (y x), where yx e [0, x). ( ~ k)l 

Hence This proves inequality (8.7). The first part of the following lemma is equivalent to Eq. (8.8). We leave out the proof of the second part. 

Lemma 8.4 Suppose We^'flR) and supp W C [0, oo) and denote by fx(q) the restriction of e~ qx to {q^O}. Then W($ fx( ) g(x) dx) 

= jg(x)W{f x(-))dx for all geS?(R + ). Furthermore — W(f x(-))  

> (X X

\dx Jx 

Remark. Lemmas 8.1-8.4 can immediately be generalized to the case of several variables. 

Lemma 8.5 ([26], p. 31). Let T(t,s) be a distribution in the dual space of y(IR + )® ^(IR) and suppose that for ί > 0 its real and imaginary parts satisfy the Cauchy-Riemann conditions    

> /Ί s) pi p\

—— Re T = —— Im T, —— Im T — — — - Re T.

dt ds dt ds Then T(t, s) = G(τ), τ = t + is, for some function G which is analytic in the open right half plane {τ : Reτ > 0}. 

Lemma 8.6 ([26], p. 239). Let G(τ) be a function, analytic in the open right half plane, satisfying the inequality 

|G(τ)|^M(l + | τ | / r α

, (8.10) 

for some positive constants M, α, β and for t = Reτ > 0. Then G(τ) is the Fourier-Laplace transform G(τ)= \ e~ x*G(a) da of some distribution 

Lemma 8.7 Let T(t, s) be as in Lemma 8.5. Then there is a distribution Ge y'(lR + ), such that T is the Fourier-Laplace transform of G, T(t,s)= $e-* {t + is) 

G(a)da=G{τ) for ί > 0 , τ = t + is. 

G(τ) is holomorphic for R e τ > 0 . Axioms for Euclidean Green's Functions 109 

Proof. By Lemma 8.5, T(ί, s) = G(τ) for some function G which is analytic in the open right half plane. We prove that G(τ) satisfies in-equality (8.10) for some positive constants M, α, β. Then Lemma 8.7 follows from Lemma 8.6. Let τ 0 = ί0 -h is 0, t 0 > 0. Then for all r e (0, ί0)G(τ o) = 1 2 π 

2π 

> 3 ίn

Let h(r) be a C 0 0 function with compact support in [^,f] and suppose J h(r)r dr = 1. Then /z ίo (r) = t$ 2h{tQ 1 r) has its support in 

\h tQ {r)rdr=l. Furthermore by Fubini's theorem and G(τ 0) 2π 

> 2 π

- ^ is)h f0 (l/ί 2 + s2) dt ds 2π J T(ί, 5) A f0 (]/(ί - ί 0 )2 + (s - s 0)2) dt ds .Hence by the properties of T there is an y'-norm such that , and a constant c, Inequality (8.10) follows from (8.11). This proves Lemma 8.7. 

Lemma 8.8 Let S n(ξ 1,... ξn) be a distribution in &"(lR%' n), and set for m= 1,2,... n, 

/or ^ e ^ ί l R t ^ " 1 ^ ® . ^ ^ 3 ) ® ^ ^ ' ^ " ^ ) . ^st/m^ ί/iαί /or α // fm

and w = 1,2 ... n, S (nm) (^»/m) cαw fee extended to a function S{™\ίlJm) which is analytic in {ζ° = £° + / ^ , ξ° > 0 } and ί/iαί S^ m) /s ί/ίe Fourier-Laplace transform of a distribution Sί, m) (^m»/m) / Π ^'flR + ), 

Then Sn{ξ l7 ... ξn) is the Fourier-Laplace transform of a distribution     

> ~Σ (
> ?k -1

Wn(qί -q,,)d*"q. (8.12) 110 K. Osterwalder and R. Schrader: 

Proof. We prove the lemma for n = 2; the proof for arbitrary n is then straightforward. Let / ^ , ξ2) e ^(ΪR 3)® ^(\R%) and Λ(ξ?) e cS^(lR + ). Then S 2 ( Λ x / 1 ) = ί S 2 ( ξ 1 , ξ 2 ) f t ( ξ ? ) / i ( i i | 2 ) ^ ί i ^ ξ 2 (8.13) for some distribution S(21 )  

> (^I,/I)G

<5^'(IR + ), according to the assumption of the lemma. By Lemma 8.4 we can change the order of integration in (8.13) and obtain 

## ί ^ ? 1 ) ^ ? (8.14) 

where % ? ) = \ e'^^hiξ^) dξl \ {q^O} is an element in ^0R + ). By Lemma 8.2 the right hand side of (8.14) defines a bilinear continuous functional on y(ΪR + ) x (^0R 3)(g)^(lRt)) and thus by the nuclear theorem a unique distribution ^ ( g ? , £ x, ξ2) in the dual space of ^(IR + )® ^(1R 3)R+). Taking the Fourier transform with respect to ξ9 we obtain where W2(qι, ξ2) is now a distribution in the dual space of «^(Rt)®^(IRt). Now take / ( ^ ) G ^(IR^), g(^) e .^(1R +), /i(ξ 2) G 5^(1R 3). Then /(gi)= j / ~ ' ! ^ ~ l i l i l /(ξi) ^ 4 ξi \ {q°ι ^ 0} is in ^(1^) and ^2!/ x 9 x fy^W^if x 9 x h). According to the assumption of the lemma, is a real analytic function in ξ° 2 >0 and it can be written as W2{f, ξ 2, h) = J e-^«S ^ 22

( / , q° 2, h) dq° 2 for some distribution Wi(f, q° 2, h) in «9"(ΪR +). As before we obtain S2 (/ x 0 x Λ) = j g(q° 2) WHf, q° 2, h) dq° 2 , (8.15) and the right hand side of (8.15) defines a bilinear continuous functional on ^(lt)><^(^-f)_><^(IR 3

)_and^thus a distribution Wiiq^q^ξi) i n 

the dual space of ^flRt)® ^(1R + )® ^(1R 3

). Taking the Fourfer transform with respect to ξ2 we finally obtain 

qJdU ιd4

q2, (8.16) where W(q li q2) is now a distribution in y(ΪR+' 2

), and h is the Fourier transform of h. Again by Lemma 8.4 we obtain (8.12) from (8.16). Axioms for Euclidean Green's Functions 111 

Acknowledgements. We are extremely grateful to Prof. A. Jaffe for proposing this work and for calling our attention to the many advantages of a Euclidean approach to constructive quantum field theory. We also thank him for his permanent interest in our work and for many fruitful conversations. It is a pleasure to thank Prof. L. Ehrenpreis for a very helpful conversation. 

References 

1. Borchers,H. J.: On structure of the algebra of field operators. Nuovo Cimento 24, 214 (1962). 2. Dimock,J., Glimm,J.: Measures on the Schwartz distribution space and applications to quantum field theory (to appear). 3. Dyson,F.J.: The S matrix in quantum electrodynamics. Phys. Rev. 75, 1736 (1949). 4. Feldman,J.: A relativistic Feynman-Kac formula. Harvard preprint (1972). 5. GelfandJ.M., Shilov,G.E.: Generalized functions, Vol. 2. New York: Academic Press 1964. 6. GΓimm,J., Jaffe, A.: Quantum field theory models, in the 1970 Les Houches lectures. Dewitt,C, Stora,R. (Ed.). New York: Gordon and Breach Science Publishers 1971. 7. Glimm,J., Jaffe, A.: Positivity of the φ\ Hamiltonian, preprint 1972. 8. Glimm,J., Jaffe, A.: The λψ\ quantum field theory without cutoffs IV. J. Math. Phys. 13, 1568(1972). 9. Glimm,J., Spencer,T.: The Wightman axioms and the mass gap for the 0> (φ) 2

quantum field theory, preprint (1972). 10. Hall, D., Wightman, A. S.: A theorem on invariant analytic functions with applications to relativistic quantum field theory. Mat.-Fys. Medd. Danske Vid. Selsk. 31, No. 5 (1951). 11. Hδrmander,L.: On the division of distributions by polynomials. Arkiv Mat. 3, 555 (1958). 12. Jost, R.: The general theory of quantized fields. Amer. Math. Soc. Publ., Providence R. I., 1965. 13. Jost,R.: Eine Bemerkung zum CTP-Theorem. Helv. Phys. Acta 30, 409 (1957). 14. Jost,R.: Das Pauli-Prinzip und die Lorentz-Gruppe. In: Theoretical physics in the twentieth century, ed. Fierz,M., Weisskopf, V. New York: Interscience Publ. 1960. 15. Nelson, E.: Quantum fields and Markoff fields. Amer. Math. Soc. Summer Institute on PDE, held at Berkeley, 1971. 16. Nelson,E.: Construction of quantum fields from Markoff fields, preprint (1972). 17. Nelson, E.: The free Markoff field, preprint (1972). 18. Osterwalder, K., Schrader,R.: Euclidean Fermi fields and a Feynman-Kac formula for Boson-Fermion models, Helv. Phys. Acta, to appear, and Phys. Rev. Lett. 29, 1423 (1972). 19. Robertson, A. P., Robertson, W. J.: Topological vector spaces. London and New York: Cambridge Univ. Press 1964. 20. Ruelle, D.: Connection between Wightman functions and Green functions in P-space. Nuovo Cimento 19, 356 (1961). 21. Schwinger,J.: On the Euclidean structure of relativistic field theory. Proc. Natl. Acad. Sci. U.S. 44, 956 (1958). 22. Schwinger,J.: Euclidean quantum electrodynamics. Phys. Rev. 115, 721 (1959). 23. Streater,R.F., Wightman,A.S.: PCT, spin and statistics and all that. New York: Benjamin 1964. 24. Symanzik, K.: Euclidean quantum field theory. I. Equations for a scalar model. J. Math. Phys. 7, 510(1966). 112 K. Oslerwalder and R. Schrader: Axioms for Euclidean Green's Functions 25. Symanzik,K.: Euclidean quantum field theory. In: Proceedings of the International School of Physics "ENRICO FERMI", Varenna Course XLV, ed. Jost,R. New York: Academic Press 1969. 26. Vladimirov, V. S.: Methods of the theory of functions of several complex variables. Cambridge and London: MIT Press 1966. 27. Whitney, H.: Analytic extensions of differentiable functions defined in closed sets. Trans. Amer. Math. Soc. 36, 63 (1934). 28. Wightman, A. S.: Quantum field theory and analytic functions of several complex variables. J. Indian Math. Soc. 24, 625 (1960). Konrad Osterwalder Lyman Laboratory of Physics Harvard University Cambridge, Mass. 02138, USA
