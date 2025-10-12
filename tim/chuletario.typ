#import "@local/chuletario:1.0.0": conf

#import "@preview/theorion:0.4.0": *
#import cosmos.rainbow: *
#show: show-theorion

// 1. Change the counters and numbering:
#set-inherited-levels(1)
#set-zero-fill(true)
#set-leading-zero(true)
#set-theorion-numbering("1.")

// 2. Other options:
// #set-result("noanswer") // Deletes the demos.
// #set-qed-symbol[#math.qed] // Changes qed symbol for proofs.

#show: conf.with(
  title: "Chuletario Teoría de la Integral y la Medida",
  author: "Álvaro Grande Blázquez",
  course: "2025 ~ 2026",
  watermark: "AGB",
)

= Introducción

#definition(title: "Integral de Riemann")[
  Sea $f: [a, b] -> RR$ acotada y sea $cal(P) = {a = x_0 < x_1 < ... < x_n = b}$ una partición del intervalo $[a, b]$.
  Sea $I_j = [x_(j-1), x_j], thick j = 1, 2, ...$ y sean también $s_j = sup_(I_j)f(x) thick "y" thick inf_(I_j)f(x)$.
  Definimos las *sumas superior e inferior*, respectivamente, como:

  $ cal(U)_f (cal(P)) = sum_(j=1)^n s_j (x_j - x_(j-1)) quad ; quad cal(L)_f (cal(P)) = sum_(j=1)^n i_j (x_j - x_(j-1)) $

  Decimos entonces que $f$ es *integrable en el sentido de _Riemann_* si existen particiones que permitan aproximar las sumas anteriores de forma arbitraria.
]

#theorem[
  Toda función $f$ continua definida en un intervalo cerrado es integrable en el sentido de _Riemman_.
  Lo mismo es cierto si $f$ es acotada y tiene solo un número finito de discontinuidades.
]

#theorem(title: "de Lebesgue")[
  Sea $f: [a, b] -> RR$ acotada. Las dos afirmaciones siguientes son equivalentes:

  - $f$ es integrable en el sentido de _Riemann_.
  - El conjunto de discontinuidades de $f$, es decir, 
  $ cal(D)_f = {x in [a, b]: f "no es continua en x"} $
  verifica la propiedad de que $forall epsilon > 0$ podemos encontrar un cubrimiento numerable de $cal(D)_f$ por intervalos abiertos:

  $ {(a_j, b_j)_(j>=1)} quad "tal que" quad sum_(j=1)^oo (b_j - a_j) < epsilon $

  Los conjuntos con esta propiedad se denominan de *medida cero*.
]

#definition(title: "Medida (exterior) de Lebesgue")[
  Dado un conjunto $A subset RR$, se define su *"medida" (exterior) de _Lebesgue_* como:
  $ m^*(A) = inf{sum_(k>=1) "long"(I_k), thick {I_k} "intervalos y" thick union.big_(k>=1)I_k supset A } $
]

#lemma[
  Un conjunto $A subset RR$ tiene medida (exterior) de _Lebesgue_ cero si y solo si
  $ forall epsilon > 0, quad exists {I_k} "sucesión de intervalos con" thick union.big_(k>=1)I_k supset A, thick "tal que" thick sum_(k>=1)"long"(I_k) < epsilon $
]

#property(title: "Propiedades de la medida exterior de Lebesgue")[
  - $m^*(emptyset) = 0$
  - Si $A subset B$ entonces $m^*(A) <= m^*(B)$.
  - Dada una familia numerable de subconjuntos, ${A_k}_k$, entonces 
  $ m^*(union.big_(k>=1) A_k) <= sum_(k>=1) m^*(A_k) $
  - La unión numerable de conjuntos de medida cero tiene medida cero.
]

#lemma[
  Si $I subset RR$ es un intervalo, entonces $"med"(I) = "long(I)"$.
]

#definition[
  $A subset [0, 1]$ es *medible* si $m^*(A) + m^*(cal(C)A) = 1$, con $cal(C)A = [0, 1] without A$.
]

#theorem(title: "Teorema Fundamental del Cálculo")[
  Sea $f$ continua y $F(x) = integral_0^x f(x) d y$. Entonces $F$ es derivable y $F'(x) = f(x) thick forall x$.
]

= Teoría general de la medida y los teoremas de convergencia

#definition(title: "Sigma álgebra")[
  Dado un conjunto $X$, se dice que $cal(A) subset cal(P)(X)$ es una *$sigma$-álgebra* si verifica:

  - $X in cal(A)$.
  - $cal(A)$ es cerrada por complementación; esto es que $A in cal(A) => A^c in cal(A)$.
  - $cal(A)$ es cerrada por uniones numerables, finitas o no; esto es que

  $ A_n in cal(A) => union.big_(n>=1) A_n in cal(A) $
]

#lemma[
  Si ${cal(A)_alpha}_(alpha in cal(D))$ es una colección arbitraria de $sigma$-álgebras, entonces $inter.big_(alpha in cal(D)) cal(A)_alpha$ es una $sigma$-algebra.
]

#definition(title: "Sigma álgebra de Borel")[
  En $RR$ se define la *$sigma$-álgebra de _Borel_* ($cal(B)_RR$) como aquella generada por  los intervalos abiertos:
  $ {(a, b): thick a, b in RR, thick a < b} $
]

#definition(title: "Medida")[
  Dada una $sigma$-álgebra $cal(A)$ en X. Se dice que $mu: cal(A) -> [0, oo]$ es una *medida* sobre $(cal(A))$ si:

  - $mu(emptyset) = 0$
  - Para toda familia numerable ${A_j}_(j>=1)$ de $cal(A)$ cuyos elementos son disjuntos dos a dos:
  $ mu(union.big.plus_(j>=1) A_j) = sum_(j>=1) mu(A_j) $
]

#definition(title: "Espacio de medida")[
  Llamaremos *espacio de medida* a toda terna $(X, cal(A), mu)$ compuesta por un conjunto $X$, una $sigma$-álgebra $cal(A)$ de $cal(P)(X)$, y una medida $mu$ definida sobre $cal(A)$.
  Diremos que la medida $mu$ sobre $cal(A)$ es *finita* si $mu(X) < oo$ y que es *$sigma$-finita* si podemos escribir $X = union.big_(n>=1) X_n$, con $X_n in cal(A)$, $n = 1, 2, 3, ...$ y $mu(X_n) < oo$.
]

#proposition[
  Sea $mu$ una medida sobre la $sigma$-álgebra $cal(A)$, se tienen los siguientes resultados:

  - Si $A, B in cal(A)$, con $A subset B$, entonces $mu(A) <= mu(B)$. Además, si $mu(A) < oo$ se tiene que $mu(B without A) = mu(B) - mu(A)$.
  - Si $A_n in cal(A)$ y $A_n subset A_(n+1) thick forall n$, entonces:
  $ mu(union.big_(j=1)^oo A_j) = lim_(j->oo) mu(A_j) $
  - Si $A_n in cal(A)$, $A_n supset A_(n+1) thick forall n$ y $mu(A_N) < oo$ para algún $N$, entonces:
  $ mu(inter.big_(j=1)^oo A_j) = lim_(j->oo)mu(A_j) $
]

#definition[
  Diremos que $f: X -> RR$ es *$cal(A)$-medible* si $forall a in RR$ se tiene que 
  $ f^(-1)((a, oo)) = {x in X: f(x) > a} in cal(A) $ 
]

#lemma[
  Dada $f: X -> RR$ $cal(A)$-medible, la familia:
  $ cal(A)_f = {B subset RR: f^(-1)(B) in cal(A)} $
  es una $sigma$-álgebra en $RR$. En consecuencia, contiene a $cal(B)_RR$ porque $(a, oo) in cal(A)_f thick forall a$.
]

#proposition[

  - Si $f, g: X -> RR$ son medibles, entonces $max(f, g)$ y $min(f, g)$ son medibles.
  - El supremo y el ínfimo de una familia numerable de funciones medibles son medibles.
  - El límite superior, el límite inferior y el límite de funciones medibles son todos medibles.
  - Si $f, g: X -> RR$ son medibles, entonces su suma $f + g$ es también medible.
  - Si $f: X -> RR$ es $cal(A)$ medible y $g: RR -> RR$ es continua, la composición $g compose f$ es $cal(A)$-medible.
]

#definition(title: "Función característica")[
  Dado un conjunto $A$, se define la *función característica (o indicatriz)* de $A$ como:

  $ chi_A (x) = cases(1 "si" x in A, 0 "si" x in.not A) $
]

#definition(title: "Función simple")[
  Dado un espacio de medida $(X, cal(A), mu)$, se dice que $s: X -> RR$ es una *función simple* si se puede escribir como una combinación lineal de funciones características de conjuntos de $cal(A)$. Es decir:

  $ s(x) = sum_(j=1)^n c_j chi_(A_j) (x), quad "con" c_j in RR, thick A_j in cal(A), thick j = 1, 2, 3, ..., n $
]

#definition(title: "Integración de funciones simples")[
  Para una función simple $s(x) = sum_(j=1)^n c_j chi_(A_j) (x)$, se define su integral como:

  $ integral_X s(x) d mu = sum_(j=1)^n c_j mu(A_j) $

  siempre que o bien $mu(A_j) < oo$ para todo $j=1, 2, ..., n$, o bien los $c_j$ sean positivos, en cuyo caso no importa que los $A_j$ sean de medida finita o no.
]

#definition(title: "Integración de funciones medibles")[
  Para una función medible $f$, con $f(x) >= 0 thick forall x$, se define su integral como sigue:

  $ integral_X f(x) d mu = sup{integral_X s(x) d mu : 0 <= s(x) <= f(x), thick s(x) "simple"} $
]

#note-box()[
  - El supremo en esta definición podría valer $oo$.
  - f puede alcanzar valores infinitos siempre que el conjunto $f^(-1)(oo)$ sea medible.
]

#proposition[
  - Sean $u, v$ funciones simples, entonces $u + v$ es simple y $integral(u+v) d mu = integral u d mu + integral v d mu$
  - Sean $f, g$ funciones medibles tal que $0 <= g <= f$, entonces $integral g d mu <= integral f d mu$
]

#definition(title: "Función densidad")[
  Si $(X, cal(A), mu)$ es un espacio de medida y $s(x) = sum_(j=1)^n c_j chi_(A_j) (x)$ es una función simple positiva, entonces la función $nu: cal(A) -> [0, oo]$ dada por:

  $ nu(A) = integral_A s(x) d mu(x) = integral_X s(x) chi_A (x) d mu(x) $

  define una medida sobre $cal(A)$. Escribiremos $d mu = s d mu$ y diremos que $s$ es la *función densidad (o función derivada)* de $nu$ con respecto a $mu$.
]

#theorem(title: "Teorema de la convergencia monótona")[
  Si ${f_j}_(j=1)^oo$ es una sucesión monótona creciente de funciones medibles positivas $(0 <= f_1 <= ... <= f_n <= f_(n+1) <= ...)$ y sea $f(x) = lim_(n->oo) f_n (x)$. Entonces se tiene:

  $ integral_X (lim_(n->oo) f_n (x)) d mu = integral_X f(x) d mu = lim_(n->oo) (integral_X f_n (x) d mu) $
]

#corollary(title: "Convergencia monótona para series")[
  Sea ${g_n (x)}_(n=1)^oo$ una sucesión de funciones medibles y positivas. Entonces:

  $ integral_X (sum_(n=1)^oo g_n (x)) d mu = sum_(n=1)^oo (integral_X g_n (x) d mu) $
]

#lemma[
  Sea $f$ una función medible y positiva. Entonces existe una sucesión monótona creciente de funciones simples positivas $0 <= s_1 <= s_2 <= ... <= s_n <= s_(n+1) <= ...$ tal que:

  $ lim_(n->oo) s_n (x) = f(x), quad forall x $
]
