#import "@local/chuletario:1.0.0": conf

#import "@preview/theorion:0.4.1": *
#import cosmos.rainbow: *
#show: show-theorion

// 1. Change the counters and numbering:
#set-inherited-levels(1)
#set-zero-fill(true)
#set-leading-zero(true)
#set-theorion-numbering("1.1")

// 2. Other options:
// #set-result("noanswer") // Deletes the demos.
// #set-qed-symbol[#math.qed] // Changes qed symbol for proofs.

// Prevents theorem boxes from breaking (also definitions, lemmas, ... and so on)
#show figure: set block(breakable: false)

// Makes corollary numbering same as the rest of objects.
#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  counter: theorem-counter,
  render: render-fn.with(fill: fuchsia.darken(10%)),
)

#show: conf.with(
  title: "Chuletario Teoría de la Integral y la Medida",
  author: "Álvaro Grande Blázquez",
  course: "2025 ~ 2026",
  watermark: "AGB",
)

// #show sym.emptyset: set text(font: ())

= Introducción

== La integral hasta 1900. La integral de Riemann

#definition(title: "Integral de Riemann")[
  Sea $f: [a, b] -> RR$ acotada y sea $cal(P) = {a = x_0 < x_1 < ... < x_n = b}$ una partición del intervalo $[a, b]$.
  Sea $I_j = [x_(j-1), x_j], thick j = 1, 2, ...$ y sean también $s_j = sup_(I_j)f(x) thick "y" thick inf_(I_j)f(x)$.
  Definimos las *sumas superior e inferior*, respectivamente, como:

  $
    cal(U)_f (cal(P)) = sum_(j=1)^n s_j (x_j - x_(j-1)) quad ; quad cal(L)_f (cal(P)) = sum_(j=1)^n i_j (x_j - x_(j-1))
  $

  Decimos entonces que $f$ es *integrable en el sentido de _Riemann_* si existen particiones que permitan aproximar las sumas anteriores de forma arbitraria.
]

#theorem[
  Toda función $f$ continua definida en un intervalo cerrado es integrable en el sentido de _Riemman_.
  Lo mismo es cierto si $f$ es acotada y tiene solo un número finito de discontinuidades.
]

#theorem(title: "Teorema Fundamental del Cálculo")[
  Sea $f$ continua y $F(x) = integral_0^x f(x) d y$. Entonces $F$ es derivable y $F'(x) = f(x) thick forall x$.
]

== La integral según Lebesgue

#definition(title: "Medida de Lebesgue")[
  Dado un conjunto $A subset RR$, se define su "medida" de Lebesgue como:

  $
    m(A) = inf{sum_(k>=1) "long"(I_k), " con" {I_k} "intervalos y " union.big_(k>=1) I_k supset A }
  $
]

#lemma[
  Un conjunto $A subset RR$ tiene medida de Lebesgue cero si y solo si
  $
    forall epsilon > 0, quad exists {I_k} "sucesión de intervalos con" thick union.big_(k>=1)I_k supset A, thick "tal que" thick sum_(k>=1)"long"(I_k) < epsilon
  $
]

#definition[
  Una determinada propiedad $cal(P)$ se dice que se cumple *en casi todo punto (c.t.p.)* si el conjunto de puntos donde NO se cumple $cal(P)$ tiene medida cero.
]

#property(title: "Propiedades de la medida de Lebesgue")[
  - $m(emptyset) = 0$
  - Si $A subset B$ entonces $m(A) <= m(B)$.
  - Dada una familia numerable de subconjuntos, ${A_k}_k$, entonces
  $ m(union.big_(k>=1) A_k) <= sum_(k>=1) m(A_k) $
  - La unión numerable de conjuntos de medida cero tiene medida cero.
]

#lemma[
  Si $I subset RR$ es un intervalo, entonces $m(I) = "long(I)"$.
]

#definition(title: "Medida exterior de Lebesgue")[

  La función sobre conjuntos definida anteriormente se denomina *medida exterior* para la medida de Lebesgue y se denota por $m^*$, es decir, $forall A subset RR$:
  $
    m^*(A) = inf{sum_(k>=1) "long"(I_k), " con" {I_k} "intervalos y " union.big_(k>=1)I_k supset A }
  $

  Según veremos posteriormente, existe una clase de subconjuntos, que denominaremos *medibles*, sobre los cuales $m^*$ será numerablemente aditiva.
]

#definition[
  $A subset [0, 1]$ es *medible* si $m^*(A) + m^*(cal(C)A) = 1$, con $cal(C)A = [0, 1] without A$.
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

= Teoría general de la medida y los teoremas de convergencia

== Espacios de medida

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
  Dada una $sigma$-álgebra $cal(A)$ en X. Se dice que $mu: cal(A) -> [0, oo]$ es una *medida* (sobre $cal(A)$) si:

  - $mu(emptyset) = 0$
  - Para toda familia numerable ${A_j}_(j>=1)$ de $cal(A)$ cuyos elementos son disjuntos dos a dos:
  $ mu(union.big.plus_(j>=1) A_j) = sum_(j>=1) mu(A_j) $
]

#definition(title: "Espacio de medida")[
  Llamaremos *espacio de medida* a toda terna $(X, cal(A), mu)$ compuesta por un conjunto $X$, una $sigma$-álgebra $cal(A)$ de $cal(P)(X)$, y una medida $mu$ definida sobre $cal(A)$.
  Diremos que la medida $mu$ sobre $cal(A)$ es *finita* si $mu(X) < oo$ y que es *$sigma$-finita* si podemos escribir $X = union.big_(n>=1) X_n$, con $X_n in cal(A)$ y $mu(X_n) < oo, thick thick n = 1, 2, 3, ...$.
]

#proposition(title: "Convergencia monótona de conjuntos")[
  Sea $mu$ una medida sobre la $sigma$-álgebra $cal(A)$, se tienen los siguientes resultados:

  - Si $A, B in cal(A)$, con $A subset B$, entonces $mu(A) <= mu(B)$. Además, si $mu(A) < oo$ se tiene que $mu(B without A) = mu(B) - mu(A)$.
  - Si $A_n in cal(A)$ y $A_n subset A_(n+1) thick forall n$, entonces:
  $ mu(union.big_(j=1)^oo A_j) = lim_(j->oo) mu(A_j) $
  - Si $A_n in cal(A)$, $A_n supset A_(n+1) thick forall n$ y $mu(A_N) < oo$ para algún $N$, entonces:
  $ mu(inter.big_(j=1)^oo A_j) = lim_(j->oo)mu(A_j) $
]

== Funciones medibles Lebesgue

#definition[
  Diremos que $f: X -> RR$ es *$cal(A)$-medible* si $forall a in RR$ se tiene que
  $ f^(-1)((a, oo)) = {x in X: f(x) > a} in cal(A) $
]

#pagebreak(weak: true)

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

  $
    s(x) = sum_(j=1)^n c_j chi_(A_j) (x), quad "con" c_j in RR, thick A_j in cal(A), thick j = 1, 2, 3, ..., n
  $
]

#block(breakable: false)[
  #definition(title: "Integración de funciones simples")[
    Para una función simple $s(x) = sum_(j=1)^n c_j chi_(A_j) (x)$, se define su integral como:

    $ integral_X s(x) d mu = sum_(j=1)^n c_j mu(A_j) $

    siempre que o bien $mu(A_j) < oo$ para todo $j=1, 2, ..., n$, o bien los $c_j$ sean positivos, en cuyo caso no importa que los $A_j$ sean de medida finita o no.
  ]
]

#definition(title: "Integración de funciones medibles")[
  Para una función medible $f$, con $f(x) >= 0 thick forall x$, se define su integral como sigue:

  $
    integral_X f(x) d mu = sup{integral_X s(x) d mu : 0 <= s(x) <= f(x), thick s(x) "simple"}
  $
]

#note-box()[
  - El supremo en esta definición podría valer $oo$.
  - $f$ puede alcanzar valores infinitos siempre que el conjunto $f^(-1)(oo)$ sea medible.
]

#proposition[
  - Sean $u, v$ funciones simples, entonces $u + v$ es simple y $integral(u+v) thick d mu = integral u d mu + integral v d mu$
  - Sean $f, g$ funciones medibles tal que $0 <= g <= f$, entonces $integral g thick d mu <= integral f thick d mu$
]

#definition(title: "Función densidad")[
  Si $(X, cal(A), mu)$ es un espacio de medida y $s(x) = sum_(j=1)^n c_j chi_(A_j) (x)$ es una función simple positiva, entonces la función $nu: cal(A) -> [0, oo]$ dada por:

  $ nu(A) = integral_A s(x) d mu(x) = integral_X s(x) chi_A (x) d mu(x) $

  define una medida sobre $cal(A)$. Escribiremos $d mu = s d mu$ y diremos que $s$ es la *función densidad (o función derivada)* de $nu$ con respecto a $mu$.
]

#theorem(title: "Teorema de la convergencia monótona")[
  Si ${f_j}_(j=1)^oo$ es una sucesión monótona creciente de funciones medibles positivas $(0 <= f_1 <= ... <= f_n <= f_(n+1) <= ...)$ y sea $f(x) = lim_(n->oo) f_n (x)$. Entonces se tiene:

  $
    integral_X (lim_(n->oo) f_n (x)) d mu = integral_X f(x) d mu = lim_(n->oo) (integral_X f_n (x) d mu)
  $
]

#corollary(title: "Convergencia monótona para series")[
  Sea ${g_n (x)}_(n=1)^oo$ una sucesión de funciones medibles y positivas. Entonces:

  $
    integral_X (sum_(n=1)^oo g_n (x)) d mu = sum_(n=1)^oo (integral_X g_n (x) d mu)
  $
]

#lemma[
  Sea $f$ una función medible y positiva. Entonces existe una sucesión monótona creciente de funciones simples positivas $0 <= s_1 <= s_2 <= ... <= s_n <= s_(n+1) <= ...$ tal que:

  $ lim_(n->oo) s_n (x) = f(x), quad forall x $
]

#proposition(title: "Desigualdad de Chebyshev")[
  Si $f$ es medible y $a>0$, se tiene:

  $ mu ({x in X: abs(f(x)) >= a}) <= 1/a integral_X abs(f(y)) d mu(y) $
]

#proposition[
  Si $f, g >=0$ son medibles, entonces:

  $ integral_X (f+g) d mu = integral_X f thick d mu + integral_X g thick d mu $
]

#lemma(title: "Fatou")[
  Dada una sucesión de funciones medibles y positivas ${f_n}$, se tiene:

  $
    integral_X (liminf_(n->oo) thick (f_n (x))) d mu <= liminf_(n->oo) thick (integral_X f_n (x) d mu)
  $
]

#definition[
  Se dice que $f$ es *integrable* si $integral f^+ d mu < oo thick$ y $thick integral f^- d mu < oo$ y escribimos:

  $ integral f thick d mu = integral f^+ thick d mu - integral f^- thick d mu $
]

#theorem(title: "Teorema de la Convergencia Dominada")[
  En $(X, cal(A), mu)$ espacio de medida, si la sucesión de funciones medibles ${f_n (x)}_(n=1)^oo$ converge puntualmente a una función $f(x)$ y además $abs(f_n (x)) <= F(x) thick forall n, thick forall x$ con $F$ medible, positiva y tal que $integral_X F(x) thick d mu < oo$, entonces $f(x)$ es integrable y se tiene:

  $ lim_(n->oo) integral_X abs(f_n (x) - f(x)) thick d mu = 0 $

  En particular,

  $
    integral_X (lim_(n->oo) f_n (x)) thick d mu = integral_X f(x) thick d mu = lim_(n->oo) (integral_X f_n (x) thick d mu)
  $
]

#corollary[
  Si ${f_k}_(k=1)^oo$ son medibles y $sum_(k=1)^oo (integral abs(f_k (x)) thick d mu) < oo$, entonces la serie $f(x) = sum_(k=1)^oo f_k (x)$ converge en _c.t.p._ y

  $
    integral_X (sum_(k=1)^oo f_k (x)) thick d mu = sum_(k=1)^oo (integral_X f_k (x) thick d mu)
  $
]

#lemma[
  $
    integral_X abs(f(x)) thick d mu(x) = integral_0^oo mu({x in X : abs(f(x)) > t}) thick d t
  $
]

#definition[
  Dado un espacio de medida $(X, cal(A), mu)$ se define la clase de funciones "integrables" como:

  $
    L^1(d mu) = {f : X -> CC "tal que" f "es medible y" integral_X abs(f) d mu < oo}
  $
]

#pagebreak(weak: true)

= Espacios de medida

#definition(title: "Espacio de medida")[
  Un *espacio de medida* es una terna $(X, cal(A), mu)$ donde $X$ es un conjunto, $cal(A)$ es una $sigma$-álgebra y $mu$ es una medida.
  Un espacio de medida $(X, cal(A), mu)$ se denomina *de Probabilidad* si se cumple $mu(X) = 1$.
]

#definition(title: "Medida completa")[
  Una medida $mu$ sobre una $sigma$-álgebra $cal(A)$ se dice que es una *medida completa* si $cal(A)$ contiene a todos los subconjuntos de conjuntos (de $cal(A)$) con medida cero, es decir:

  Si $A in cal(A)$ con $mu(A) = 0$, entonces $forall E subset A$ se tiene que $E in cal(A)$ y obviamente que $mu(E) = 0$.
]

#theorem[
  Sea $(X, cal(A), mu)$ un espacio de medida, definimos:

  - $overline(cal(A)) = {E subset X : forall A, B in cal(A) "con" A subset E subset B thick "y" thick mu(B without A) = 0}$
  - Si $E in overline(cal(A))$ con $A subset E subset B$ y $mu(B without A) = 0, thick thick overline(mu)(E) = mu(A)$

  Entonces:

  - $overline(cal(A))$ es una $sigma$-álgebra (la más pequeña) que contiene a $cal(A)$.
  - $overline(mu)$ es una medida completa que extiende a $mu$.
]<thm:complete>

#proposition[
  Sea $(X, cal(A), mu)$ con $mu$ completa, entonces:

  - Si $f = g$ en _c.t.p._ y $f$ es medible, entonces $g$ es medible.
  - Si las $f_n$ son medibles $forall n$ y $thick f_n -> f thick$ para _c.t.p._, entonces $f$ es medible.
]

#pagebreak(weak: true)

#definition(title: "Medida exterior")[
  Se dice que $mu^* : cal(P)(X) -> [0, oo]$ es *medida exterior* si cumple:

  - $mu^*(emptyset) = 0$
  - Si $A subset B, quad mu^*(A) <= mu^*(B)$

  - $mu^* (union.big_(i=1)^oo A_i) <= sum_(i=1)^oo mu^* (A_i)$
]

#definition(title: "Premedida")[
  Dada una álgebra $cal(B)_0 subset cal(P)(X)$, se dice que $mu_0 : cal(B)_0 -> [0, oo]$ es una *pre-medida* si verifica:

  - $mu_0(emptyset) = 0$
  - Si $B_i in cal(B)_0$ son disjuntos y $thick union.big.plus_(i=1)^oo B_i in cal(B)_0$, entonces $mu_0(union.big.plus_(i=1)^oo B_i) = sum_(i=1)^oo mu_0(B_i)$
]

#definition(title: "Conjuntos medibles para una medida exterior")[
  Dada una medida exterior $mu^*$ sobre $X$, se dice que $A subset X$ es *$mu^*$-medible* (o medible con respecto a $mu^*$) si:

  $ mu^*(E) = mu^*(E inter A) + mu^*(E inter A^c) quad forall E subset X $

  Denotamos $cal(A)^* = {A subset X : A "es" mu^*"-medible"}$
]

#theorem(title: "Teorema de Carathéodory I")[
  Si $mu^*$ es una medida exterior sobre $X$ y definimos $cal(A)^*$ como antes. Entonces $cal(A)^*$ es una \ $sigma$-álgebra y $mu^*|_(cal(A)^*)$ (restricción de $mu^*$ a $cal(A)^*$) es una medida completa.
]

#theorem(title: "Teorema de Carathéodory II")[
  Sea $mu_0$ una pre-medida sobre $B_0$ y definamos una medida exterior $mu^*$ y la clase $cal(A)^*$ de los \ $mu$-medibles como antes. Entonces:

  - $cal(A)^*$ es una $sigma$-álgebra que contiene a $B_0$
  - $mu = mu^*|_(cal(A)^*)$ es una medida completa que extiende a $mu_0$
]<thm:caratheodory2>

#definition(title: "Medida de Lebesgue")[
  Sea el álgebra $cal(B)_0$ generada por los intervalos de la forma $(a, b]$, con $(a < b : a, b in RR)$.
  Es decir, $cal(B)_0$ está formada por las uniones finitas de esos intervalos y sus complementarios.

  Definimos $mu_0((a, b]) = b - a$ y extendemos la definición de $cal(B)_0$ de manera obvia. Entonces:

  - $mu^*$ es la medida exterior de Lebesgue
  - $cal(A)^*$ es la $sigma$-álgebra de los conjuntos medibles de Lebesgue
  - $mu = mu^*|_(cal(A)^*)$ es la medida de Lebesgue ($mu(I) = "long"(I), thick forall I$ intervalo)
]

#definition(title: "Medidas de Lebesgue-Stieltjes")[
  Con más generalidad, si $F : RR -> RR$ es creciente y continua por la derecha podemos definir $mu_0 = mu_F$ sobre el álgebra $cal(B)_0$ anterior, $mu_F ((a, b]) = F(b) - F(a)$ y $mu_F$ es una pre-medida.
]

#note-box[
  La medida dada por la extensión de Carathéodory se denota por $mu = d F$.
  En particular, si $F(x) = x$ estamos en el caso de la medida de Lebesgue, que se denota por $d x$.
]

#important-box[
  Si $(X, cal(A), mu)$ es un espacio de medida y $mu$ no es completa, entonces hay dos formas de completarla:

  - Por el @thm:complete, se obtiene $(X, overline(cal(A)), overline(mu))$
  - Por el @thm:caratheodory2 (Carathéodory), se obtiene $(X, cal(A)^*, mu^*|_(cal(A)^*))$, tomando a $mu^*$ la medida exterior inducida por $mu$ que, al ser medida, también es pre-medida.
]

#lemma[
  Si $mu$ es $sigma$-finita entonces las dos extensiones coinciden, es decir, $overline(cal(A)) = cal(A)^*$.
]

#pagebreak(weak: true)

#definition(title: "Medida de Borel")[
  Se dice que $mu$ es una *medida de Borel* en $RR$ si está definida sobre la $sigma$-álgebra de los conjuntos de Borel $cal(B)_RR$.
]

#lemma[
  Toda pre-medida $mu_F$ definida como antes sobre $cal(B)_0$ se puede extender (de forma única) a una medida de Borel.
]

#lemma[
  Si $m$ es medida de Lebesgue y denotamos por $cal(L)$ los conjuntos medibles de Lebesgue, entonces $cal(B)_(RR) subset.neq cal(L) subset.neq cal(P) (RR)$ (contenidos estrictos).
]

#proposition[
  Si $mu$ es una medida de Borel finita sobre conjuntos acotados, entonces $mu$ proviene de cierta pre-medida $mu_F$ sobre $cal(B)_0$.
]

#definition(title: "Medida regular")[
  Dado $(RR, cal(A), mu)$ espacio de medida, se dice que $mu$ es *regular* (en $RR$) si verifica:

  - $cal(B)_RR subset cal(A)$
  - Regularidad exterior, esto es: $mu(A) = inf thick {mu(U) : A subset U, thick U "abierto"}$
  - Regularidad interior, esto es: $mu(A) = sup thick {mu(K) : K subset A, thick K "compacto"}$
]

#proposition[
  - La medida de Lebesgue, $m$, es regular.
  - Cualquier medida de Lebesgue-Stieltjes es regular.
]

#theorem(title: "Invarianza por traslaciones y dilataciones")[
  Dado $E subset RR$, definimos para $x_0 in RR, thick r > 0; thick x_0 + E = {x_0 + y: y in E} thick "y" thick r dot E = {r dot y : y in E}$. Entonces si $E in cal(L)$ se tiene:

  - $x_0 + E in cal(A), thick thick r dot E in cal(A)$
  - $m(x_0 + E) = m(E), thick thick m(r dot E) = r dot m(E)$
]

#theorem[
  Sea $f: [a, b] -> RR$ acotada e integrable Riemann. Entonces $f$ es medible Lebesgue y por tanto integrable Lebesgue y además:

  $ integral_a^b f(x) thick d x = integral_([a, b]) f(x) thick d m $
]

= Medidas producto y el teorema del cambio de variable

#definition(title: "Rectángulo")[
  Dados intervalos $J_1, J_2, ..., J_n$ de $RR$ (finitos o no), al producto cartesiano #linebreak(justify: true) $R = J_1 times J_2 times ... times J_n$ lo denominaremos *rectángulo* en $RR^n$.
]

#definition(title: "Volumen")[
  Si $abs(J_1)_1, ..., abs(J_n)_1 != 0$, se define el *volumen* $n$-dimensional del rectángulo $R$ como:

  $ abs(R_n) = abs(J_1)_1 dot abs(J_2)_1 dot ... dot abs(J_n)_1 $

  donde $|dot|_1$ denota la longitud en $RR$.
  Si se tuviera $abs(J_k)_1 = 0$ para algún $k$, entonces se define $abs(R)_n = 0$ incluso si alguna de las otras coordenadas fuera infinita.
]

#lemma[
  - La intersección de dos rectángulos es un rectángulo.

  - La unión finita de rectángulos se puede escribir como unión disjunta y finita de rectángulos.
  - La clase $cal(B)_0 = {"Uniones finitas de rectángulos"}$ es una álgebra.
]

#definition(title: "Volumen de un elemento")[
  Definimos el *volumen de un elemento* $B in cal(B)_0$ escribiendo $B$ como la unión disjunta de rectángulos, $B = union.big.plus_(j=1)^m R_j$ y poniendo $abs(B) = sum_(j=1)^m abs(R_j)$.
]

#lemma[
  $|dot|$ es una premedida en $cal(B)_0$.
]

#let title = [Medida de Lebesgue en $RR^n$]

#definition(title: title)[
  La extensión de Carathéodory de la terna $(RR^n, cal(B)_0, |dot|_n)$ nos da un espacio de medida completa $(RR^n, cal(L)_n, m_n)$ con $m_n (R) = abs(R) thick thick forall R$ rectángulo.
  Por ser $|dot|_n$ $sigma$-finita, esta extensión es única sobre la mínima $sigma$-álgebra que contiene a $cal(B)_0$ que, como veremos, coincide con la clase de los Borel en $RR^n$.
  La clase $cal(L)_n$ es la $sigma$-álgebra de Lebesgue en $RR^n$ y $m_n = m = d x$ la medida de Lebesgue.
]

#let title = [Propiedades de la $sigma$-álgebra y de la medida de Lebesgue en $RR^n$]
#property(title: title)[
  - $cal(L)_n$ contiene a los abiertos de $RR^n$ y por tanto a la $sigma$-álgebra de Borel, $cal(B)_n$. (Ver @lema-prop-med-lebesgue)

  - $forall A in cal(L)_n, thick thick m(A) = inf{sum_(i=1)^oo abs(R_i): thick R_i "rectángulos", thick union.big_(i=1)^oo R_i supset A}$

  - La medida de Lebesgue en $RR^n$ es regular, es decir:

  $
    m(A) = inf{m(U) : A subset U, thick U "abierto"} \
    m(A) = sup{m(K) : K subset A, thick K "compacto"}
  $

  - La medida de Lebesgue en $RR^n$ es invariante por traslaciones.
]

#definition(title: "Cubos diádicos")[
  Para cada $k in ZZ$, sea $Delta_k$ el conjunto de cubos de $RR^n$ de lado $2^(-k)$ y esquinas en el conjunto:

  $ 2^(-k)ZZ^n = {2^(-k) (v_1, ..., v_n) : v_j in ZZ} $

  Llamamos $Delta$ a la unión de todos los $Delta_k$.
]

#property(title: "Propiedades de los cubos diádicos")[
  - Para cada entero $K$, $Delta_k$ forma una partición de $RR^n$.

  - Todos los cubos de $Delta_k$ tienen el mismo lado, de longitud $2^(-k)$.

  - Sean $R, Q$ dos cubos en $Delta$. Si $circle(Q) inter circle(R) = emptyset$, entonces o bien $Q subset R$ o bien $R subset Q$.

  - Cada $Q in Delta_k$ se puede escribir como unión de $2^n$ cubos de $Delta_(k+1)$ con interiores disjuntos.
]

#lemma[
  Todo abierto es unión numerable casi disjunta de cubos de $RR^n$, es decir, dado $U$ abierto, $exists {Q_j}$ cubos con interiores disjuntos tales que $U = union.big_i Q_i$.
  Eligiendo cubos de la forma $Q = J_1 times J_2 times ... times J_n$ con $J_k = (a_k, a_k + h]$, la unión es, de hecho, disjunta.
] <lema-prop-med-lebesgue>

#theorem[
  - Si $A in cal(L)_n, thick x_0 in RR^n$ entonces $x_0 + A in cal(L)_n$ y $m(x_0 + A) = m(A)$

  - Sea $f$ medible $f: RR^n -> RR$, si $f>=0$ o $f in L^1(RR^n, d m)$ se tiene $forall x in RR^n$:

  $ integral f(x_0 + x) d m = integral f(x) d m $
]

#theorem[
  - Si $A in cal(L)_n, thick c in RR without {0}$ entonces $c dot A in cal(L)_n$ y $m(c dot A) = abs(c)^n dot m(A)$

  - Sea $f: RR^n -> RR$ medible. Si $f>=0$ o $f in L^1(RR^n, d m)$ se tiene $forall c != 0$:

  $ integral f(c dot x) d m(x) = 1/abs(c)^n integral f(x) d m(x) $
]

#theorem(title: "Fórmula del cambio de variable para aplicaciones lineales")[
  Sea $T$ una aplicación $RR^n -> RR^n$ lineal y regular ($det(T) != 0$, i.e. la matriz que define a $T$ pertenece a $"GL"(n, RR)$).
  Entonces:

  - Si $A in cal(L)_n, thick T(A) in cal(L)_n, thick "y" thick thick m(T(A)) = abs(det(T))m(A)$

  - Sea $f: RR^n -> RR$ medible. Si $f>=0$ o $f in L^1(RR^n, d m )$ se tiene:

  $ integral f(x) d m = abs(det(T)) integral f(T(x)) d m $
]<formula-cambio-variable>

#corollary(title: "Invarianza por rotaciones")[
  Si $T$ es una rotación (de forma que $abs(det(T)) = 1$) se tiene:

  $ m(T(A)) = m(A), quad forall A in cal(L)_n $
]

#corollary[
  Si $D$ es un conjunto medible y $f$, $T$ son como en el @formula-cambio-variable, entonces se tiene:

  $ integral_(T(D)) f(y) d m = abs(det(T)) integral_D f(T(x)) d m $
]

#definition(title: "Aplicación medible")[
  Dados dos espacios $X$ e $Y$ dotados de ciertas $sigma$-álgebras $cal(A)_X$ y $cal(A)_Y$ respectivamente, se dice que $phi: X -> Y$ es *medible* (con respecto a $cal(A)_X$ y $cal(A)_Y)$ si:

  $ phi^(-1)(B) in cal(A)_X thick forall B in cal(A)_Y $
]

#definition(title: "Medida inducida")[
  Si $mu$ es una medida sobre la $sigma$-álgebra $cal(A)_X$ entonces $phi$ *induce una medida* sobre $cal(A)_Y$ de la siguiente forma:

  $ mu_phi (B) = mu(phi^(-1)(B)) $
]<definición-medida-inducida>

#theorem[
  Sean $cal(A)_X, thick cal(A)_Y, thick mu, thick mu_phi$ como la @definición-medida-inducida. Si $f: Y -> RR$ es medible y $f>=0$ o #linebreak(justify: true) $f in L^1(d mu_phi)$ entonces:

  $ integral_Y f(y) d mu_phi (y) = integral_X f(phi(x)) d mu(x) $
]

#definition(title: "Jacobiano")[
  Sea $Omega$ un abierto de $RR^n$ y $phi: Omega subset RR^n -> RR^n$ un difeomorfismo regular, es decir #linebreak(justify: true) $phi in C^1(RR^n)$, es inyectivo y su inversa $phi^(-1) in C^1(RR^n)$.
  Si $phi = (phi_1, ..., phi_n)$ son sus funciones coordenadas, entonces su diferencial en el punto $x, thick D_(phi)(x)$ es una aplicación lineal dada por la matriz jacobiana:

  $
    A_x = mat(
      (partial phi_1)/(partial x_1)(x), (partial phi_1)/(partial x_2)(x), ..., (partial phi_1)/(partial x_n)(x);
      (partial phi_2)/(partial x_1)(x), (partial phi_2)/(partial x_2)(x), ..., (partial phi_2)/(partial x_n)(x);
      dots.v, dots.v, dots.down, dots.v;
      (partial phi_n)/(partial x_1)(x), (partial phi_n)/(partial x_2)(x), ..., (partial phi_n)/(partial x_n)(x);
    )
  $

  Se denomina *jacobiano* de $phi$ en $x$ al determinante de esta matriz:

  $ J(x) = det(A_x) = det(D_phi (x)) $
]

#theorem(title: "Teorema del cambio de variable")[
  Sea $phi: Omega subset RR^n -> RR^n$ un difeomorfismo regular $C^1$ sobre el abierto $Omega$ y sea $f: phi(Omega) -> RR$ medible (Lebesgue).
  Si $f>=0$ o $f in L^1(d x)$. Entonces:

  $
    integral_(phi(Omega)) f(y) d y = integral_Omega (f compose phi(x)) dot abs(J(x)) thick d x
  $
]

#lemma[
  Si $Q$ es un cubo de $Omega$ entonces:

  $ m(phi(Q)) <= integral_Q abs(J(x)) thick d x $
]

= Teorema de Fubini

#definition(title: "Rectángulo medible")[
  Dados $A in cal(A)$ y $B in cal(B)$, definimos el *rectángulo medible*:

  $ A times B = {(x, y) : x in A, thick y in B} $
]

#lemma[
  - La intersección de rectángulos es un rectángulo.
  - La unión de un número finito de rectángulos medibles se puede escribir como la unión disjunta y finita de rectángulos medibles.

  - La familia $display(Pi_0 = {union.big_(j=1)^N (A_j times B_j) : A_j in cal(A), thick B_j in cal(B)})$ es una álgebra.
]

#definition[
  Definimos, para un rectángulo medible $R = A times B; thick A in cal(A), thick B in cal(B)$:

  $ pi_0(R) = pi_0(A times B) = mu(A) nu(B) $

  si tanto $mu(A)$ como $nu(B)$ no son $0$ y $pi_0(R) = 0$ en caso contrario.
  Dado un elemento $U in Pi_0$, lo escribimos como unión disjunta de rectángulos $U = union.big.plus_(j=1)^N (A_j times B_j)$, con #linebreak(justify: true) $A_j in cal(A), thick B_j in cal(B)$ y definimos:

  $ pi_0(U) = sum_(j=1)^N pi_0(A_j times B_j) = sum_(j=1)^N mu(A_j) nu(B_j) $
]

#lemma[
  $pi_0$ está bien definida y es una premedida en $Pi_0$.
]

#definition[
  La mínima $sigma$-álgebra que contiene $Pi_0$ se denota por $cal(A) times.circle cal(B)$.
]

#definition(title: "Espacio de medida producto")[
  El Teorema de Carathéodory (@thm:caratheodory2) nos permite extender $(X times Y, Pi_0, pi_0)$ a un espacio de medida completo $(X times Y, Pi_0^*, pi_0^* |_(Pi_0^*))$.
]

#note-box[
  Algunos libros escriben $cal(A) times cal(B)$ para denotar la $sigma$-álgebra producto, pero esto es solo por convenio.
  También se suele escribir $d mu times d nu$ en vez de $d mu times.circle d nu$, o también $d (mu times nu)$.
]

#definition[
  - Dado $E subset X times Y$ y fijado $x in X$ se define la *$x$-sección de $E$* como:

  $ E_x = {y in Y : (x, y) in E} $

  - De la misma forma, fijado $y in Y$ se define la *y-sección de $E$* como:

  $ E^y = {x in X : (x, y) in E} $

  - Para una función $f: X times Y -> RR$ se define la *x-sección de $f$*, fijado $x in X$, como:

  $
    f_x: & Y -> RR \
         & y -> f_x (y) = f(x, y)
  $

  - Análogamente, se define la *y-sección de $f$*, fijado $y in Y$, como:

  $
    f^y: & X -> RR \
         & x -> f^y (x) = f(x, y)
  $
]

#pagebreak(weak: true)

#theorem(title: "Teorema de Fubini")[
  Sea $(X, cal(A), mu)$ e $(Y, cal(B), nu)$ dos espacios de medida $sigma$-finitos.

  - Si $f: X times Y -> RR$ es medible y positiva, entonces las funciones

  $ x -> g(x) = integral_Y f_x d mu, quad quad y-> h(y) = integral_X f^y d mu $

  son medibles y además se tiene:

  $
    integral_(X times Y) f(x, y) d(mu times nu) = integral_X (integral_Y f(x, y) d nu(y)) d mu(x) = integral_Y (integral_X f(x, y) d mu(x)) d nu(y)
  $

  - Si $f: X times Y -> RR$ es integrable, es decir, $f in L^1(d(mu times nu))$, entonces:

    - $f_x in L^1(d nu)$ c.t.p. $x in X$
    - $f^y in L^1(d mu)$ c.t.p. $y in Y$
    - las funciones $g(x)$ y $h(y)$ se pueden definir en c.t.p. $x in X$, c.t.p. $y in Y$
    - $g(x)$ y $h(x)$ son integrables, es decir, $g(x) in L^1(d mu)$ y $h(x) in L^1(d nu)$

    Además se cumple:

    $
      integral_(X times Y) f(x,y) d(mu times nu) = integral_X (integral_Y f(x, y) d nu(y)) d mu(x) = integral_Y (integral_X f(x, y) d mu(x)) d nu(y)
    $
]

#proposition[
  Sean $X, cal(A), mu)$ y $(Y, cal(B), nu)$ dos espacios de medida $sigma$-finitos y si $E in cal(A) times.circle cal(B)$, entonces las funciones:

  $ x -> nu(E_x) wide wide y -> mu(E^y) $

  son medibles en $X$ e $Y$ respectivamente y además se tiene:

  $
    mu times.circle nu(E) = integral_X nu(E_x) d mu(x) = integral_Y mu(E^y) d nu(y)
  $
]

#definition(title: "Clase monótona")[
  Se dice que $cal(C) subset cal(P) (X times Y)$ es una *clase monótona* si es cerrada por uniones crecientes y por intersecciones decrecientes, esto es:

  $
    E_1 subset E_2 subset ... subset E_m subset ... in cal(C) => union.big_(m>=1) E_m in cal(C) \
    E_1 supset E_2 supset ... supset E_m supset ... in cal(C) => inter.big_(m>=1) E_m in cal(C)
  $
]

#lemma[
  Si $Pi_0$ es una álgebra y $cal(C)$ es una clase monótona con $Pi_0 subset cal(C)$, entonces la mínima $sigma$-álgebra que contiene a $Pi_0$, $sigma(Pi_0)$, está contenida en $cal(C)$.
]

#counter(heading).update(0)
#set heading(numbering: "A.1.")
#set-theorion-numbering("A.1.")

= Demostraciones relevantes <anexo>

#theorem(title: "Teorema de Borel-Cantelli")[
  Sean ${A_n}$ conjuntos medibles en un espacio de medida $(X, cal(A), mu)$ tales que #linebreak(justify: true) $sum_(n=1)^oo mu(A_n) < oo$. Entonces cada elemento de $x$ pertenece a un número finito de $A_n$ para $c. t. x.$.
  Dicho de otra manera, el conjunto de puntos $x$ que pertenecen a infinitos $A_n$, es decir, $limsup A_n$, mide 0.
]

#proof[
  Por la definición de límite superior tenemos:

  $
    mu(limsup A_n) = mu lr(size: #3em, (lim_(n->oo) lr(size: #2em, (inter.big_(n)^oo underbrace(union.big_(j=n)^oo A_j, arrow.br thick G_n \ G_1 supset G_2 supset ...))))) underbrace(=, T.C.M. \ (mu(G_n) < oo)) lim_(n->oo) (mu(union.big_(j=n)^oo A_j)) \
    <= lim_(n->oo) (sum_(j=n)^oo mu(A_j)) = 0 quad ("Criterio de Cauchy")
  $
]

#lemma(title: "Lema de Fatou")[
  Dada una sucesión de funciones medibles y positivas, ${f_n}$, se tiene:

  $
    integral_X (liminf_(n->oo) (f_n (x))) d mu <= liminf_(n->oo) (integral_X f_n (x) d mu)
  $
]

#proof[
  Es una consecuencia del _Teorema de la Convergencia Monótona_.
  Sea #linebreak(justify: true) $g_n (x) = inf{f_n, f_(n+1), f_(n+2), ...}$.
  Entonces $0 <= g_1 <= g_2 <= ... <= g_n <= g_(n+1) <= ...$ y $lim_(n->oo) g_n = liminf_(k->oo) f_k$ por definición del límite inferior.
  Además $g_n <= f_n forall n$.
  Por tanto:

  $
    integral_X (liminf_(n->oo) (f_n (x))) d mu = integral_X lim_(n->oo) g_n (x) d mu underbrace(=, T.C.M.) lim_(n->oo) integral_X g_n (x) d mu <= liminf_(n->oo) (integral_X f_n (x) d mu)
  $
]

#theorem(title: "Teorema de la convergencia monótona para conjuntos")[
  1. Si $A_n in cal(A)$ y $A_n subset A_(n+1) thick forall n$, entonces:

  $ mu(union.big_(j=1)^oo A_j) = lim_(j->oo) mu(A_j) $

  2. Si $A_n in cal(A)$, $A_n supset A_(n+1) thick forall n$ y $mu(A_N) < oo$ para algún $N$, entonces:

  $ mu(inter.big_(j=1)^oo A_j) = lim_(j->oo) mu (A_j) $
]

#proof[
  1. Definimos $B_1 := A_1$ y $thick B_n := A_n without A_(n-1)$ para $n>=2$.
    Por construcción, los $B_n$ son disjuntos y además:

    $ union.big_(j=1)^oo A_j = union.big.plus_(j=1)^oo B_j $

    Por la aditividad de la medida sobre una unión disjunta numerable:

    $ mu(union.big_(j=1)^oo A_j) = sum_(j=1)^oo mu(B_j) $

    Ahora, para cada $n$ la unión finita de los primeros $B_j$ es:

    $ union.big_(j=1)^n B_j = A_n quad => quad mu(A_n) = sum_(j=1)^n mu(B_j) $

    Al tomar $n->oo$ las sumas parciales convergen a $sum_(j=1)^oo mu(B_j)$. Por tanto:

    $ lim_(j->oo) mu(A_j) = sum_(j=1)^oo mu(B_j) = mu(union.big_(j=1)^oo A_j) $

  #pagebreak(weak: true)

  2. Trabajaremos en la cola a partir de $N$.
    Para $k>=0$ definimos $C_k := A_N without A_(N+k)$.
    Como $A_(N+k) subset A_(N+k-1)$ los conjuntos $C_k$ satisfacen $C_k subset C_(k+1)$ y además:

    $ union.big_(k=0)^oo C_k = A_N without inter.big_(j=N)^oo A_j $

    Aplicando la parte $(1)$ a la sucesión creciente $C_k$ obtenemos:

    $ mu (union.big_(k=0)^oo C_k) = lim_(k->oo) mu(C_k) $

    Pero para cada $k$ tenemos que: $mu(C_k) = mu (A_N) - mu(A_(N+k))$, porque $C_k$ y $A_(N+k)$ son disjuntos y su unión es $A_N$, y $mu(A_N) < oo$ garantiza que restas como esta son válidas.
    Entonces:

    $
      mu(A_N without inter.big_(j=N)^oo A_j) = lim_(k->oo) (mu(A_N) - mu(A_(N+k))) = mu(A_N) - lim_(k->oo) mu(A_(N+k))
    $

    Reordenando obtenemos: $mu(inter.big_(j=N)^oo A_j) = lim_(k->oo) mu(A_(N+k))$. Como los $A_n$ son decrecientes, $lim_(n->oo) mu(A_n)$ existe y coincide con el límite de la subsucesión $mu(A_(N+k))$.
    Finalmente:

    $
      inter.big_(j=1)^oo A_j = inter.big_(j=N)^oo A_j wide => wide mu(inter.big_(j=1)^oo A_j) = lim_(j->oo) mu(A_j)
    $
]

#v(-2pt)

#theorem(title: "Teorema de la Convergencia Dominada")[
  En $(X, cal(A), mu)$ espacio de medida, si la sucesión de funciones medibles ${f_n (x)}_(n=1)^oo$ converge puntualmente a una función $f(x)$ y además $abs(f_n (x)) <= F(x) thick forall n, thick forall x$ con $F$ medible, positiva y tal que $integral_X F(x) thick d mu < oo$, entonces $f(x)$ es integrable y se tiene:

  $
    quad quad lim_(n->oo) integral_X abs(f_n (x) - f(x)) thick d mu = 0 quad quad (1)
  $

  En particular,

  $
    quad quad integral_X (lim_(n->oo) f_n (x)) thick d mu = integral_X f(x) thick d mu = lim_(n->oo) (integral_X f_n (x) thick d mu) quad quad (2)
  $
]

#proof[
  El que $f$ sea integrable es inmediato porque $lim_(n->oo) f_n (x) = f(x)$ implica $abs(f(x)) <= F(x), thick forall x$ también y $F$ es integrable (finita).
  Veamos también que $(1) => (2)$:

  $
    abs(integral_X f_n (x) d mu - integral_X f(x) d mu) = abs(integral_X (f_n (x) - f(x)) d mu) <= integral_X abs(f_n (x) - f(x)) d mu ->_(n arrow oo) 0 => (2)
  $

  Luego solo necesitamos probar $(1)$.
  Veamos que es una consecuencia del lema de Fatou:
  Sean $h_n = 2F(x) - abs(f_n (x) - f(x)), thick n=1, 2, 3, ...$.
  Entonces $h_n >= 0$ y #linebreak(justify: true) $liminf_(n->oo) h_n = lim_(n->oo) h_n = 2 F(x)$.
  Por Fatou deducimos:

  $
    integral_X 2F(x) d mu <= liminf_(n->oo) integral_X h_n d mu = liminf_(n->oo)(integral_X 2 F(x) d mu - integral_X abs(f_n (x) - f(x)) d mu) = \
    = integral_X 2 F(x) d mu - limsup_(n->oo) integral_X abs(f_n (x) - f(x)) d mu
  $

  Despejando queda:

  $ limsup_(n->oo) integral_X abs(f_n (x) - f(x)) d mu <= 0 $

  y, por tanto, lo anterior debe ser igual a 0. Es decir,

  $ lim_(n->oo) integral_X abs(f_n (x) - f(x)) d mu = 0 $
]
