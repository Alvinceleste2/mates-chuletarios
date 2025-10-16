#import "@local/chuletario:1.0.0": conf

#import "@preview/theorion:0.4.0": *
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

// Makes corollary numbering same as the rest of objects.
#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  counter: theorem-counter,
  render: render-fn.with(fill: fuchsia.darken(10%)),
)

#show: conf.with(
  title: "Chuletario Cálculo Numérico II",
  author: "Álvaro Grande Blázquez",
  course: "2025 ~ 2026",
  watermark: "AGB",
)

= Interpolación polinómica de Lagrange

== El problema de interpolación de Lagrange

#definition(title: "Problema de interpolación")[
  Dados un entero no negativo $N$, $N+1$ puntos reales $x_0, x_1, ..., x_N$ distintos dos a dos y valores $f(x_0), f(x_1), ..., f(x_N)$ de una función, el *problema de interpolación* se basa en encontrar un polinomio de grado $N$ tal que:

  $ p(x_0) = f(x_0), thick p(x_1) = f(x_1), thick ..., p(x_N) = f(x_N) $

  Los $x_i$ se llaman abcisas o *nodos de la interpolación* y no tienen por qué estar ordenados.
]

#theorem[
  El problema de interpolación de Lagrange tiene solución única que se llama el *polinomio interpolador de Lagrange* de grado menor o igual que $N$ de la función $f$ en los puntos $x_0, x_1, ..., x_N$.
]

#corollary[
  Sean las condiciones anteriores, el polinomio de Lagrange también puede escribirse de la siguiente manera:

  $ p(x) = f(x_0)l_0(x) + f(x_1)l_1(x) + ... + f(x_N)l_N (x) $

  Donde $l_i (x_j) = 0, thick i != j; thick l_i (x_i) = 1$ y en particular:

  $ l_i (x) = ((x-x_0) ... (x-x_(i-1)) (x-x_(i+1)) ... (x - x_N))/((x_i - x_0) ... (x_i - x_(i-1)) (x_i - x_(i+1)) ... (x_i - x_N)) $
]

#pagebreak()

== La forma de Newton: diferencias divididas

#definition(title: "Polinomio interpolador en forma de Newton")[
  Hasta ahora hemos visto dos formas de construir el polinomio interpolador de Lagrange, por coeficientes indeterminados y la forma de Lagrange.
  Una tercera forma de realizar la construcción es la *forma de Newton*, a través de la cual nos queda el siguiente polinomio:

  $ p(x) = c_0 + c_1(x-x_0) + c_2(x-x_0)(x-x_1) + ... + c_N (x-x_0)(x-x_1)...(x-x_(N-1))$

  Por tanto, escribimos $p(x)$ en la base 

  $ cal(B) = {1, (x-x_0), (x-x_0)(x-x_1), ... (x-x_0)(x-x_1)...(x-x_(N-1))} $
]

#definition(title: "Diferencias divididas")[
  Dados un entero no negativo $N$, $N+1$ puntos $x_0, ..., x_N$ distintos dos a dos y una función definida en ellos, llamamos *diferencia dividida* de $f$ en $x_0, ..., x_N$ al coeficiente de $x^N$ en el desarrollo de potencias de $x$ del correspondiente polinomio interpolador de Lagrange.
  Esta diferencia dividida se representa como $f[x_0, x_1, ..., x_N]$.
  Al entero $N$ se le llama *orden* de la diferencia dividida.
  Así, el polinomio interpolador en forma de Newton se escribe:

  $ p(x) = f[x_0] + f[x_0, x_1](x-x_0) + f[x_0, x_1, x_2](x-x_0)(x-x_1) + ... + $

$ + ... + f[x_0, x_1, ..., x_N](x-x_0)(x-x_1)...(x-x_N) $
]

#theorem[
  Sean $x_0, x_1, ..., x_N, thick N>=1, thick N+1$ puntos distintos dos a dos donde está definida una función $f$. Entonces:

  $ f[x_0, x_1, ..., x_N] = (f[x_1, x_2, ..., x_N] - f[x_0, x_1, ..., x_(N-1)])/(x_N - x_0) $
]<dif-div>

#pagebreak()

#lemma(title: "Tabla de diferencias divididas")[
  Usando reiteradamente el @dif-div podemos construir la siguiente tabla:

#table(
  columns: 6,
  rows: 5,
  inset: 10pt,
  stroke: none,
  align: horizon,
  $ x_0 $, $ f[x_0] $, $$, $$, $$, $$,
  $ x_1 $, $ f[x_1] $, $ f[x_0, x_1] $, $$, $$, $$,
  $ x_2 $, $ f[x_2] $, $ f[x_1, x_2] $, $ f[x_0, x_1, x_2] $, $$, $$,
  $ ... $, $ ... $, $ ... $, $ ... $, $ ... $, $$,
  $ x_N $, $ f[x_N] $, $ f[x_(N-1), x_N] $, $ f[x_(N-2), x_(N-1), x_N] $, $...$ , $ f[x_0, x_1, ..., x_N]$
)

  Observamos que una vez calculada la tabla, los elementos diagonales nos dan los coeficientes del polinomio interpolador escrito en la forma de Newton.
]

== Comparación entre las formas de coeficientes indeterminados, Lagrange y Newton

#proposition[
  Hemos visto tres formas de construir el polinomio interpolador de Lagrange. Vamos a compararlas:

  - *Coste de construcción*: máximo en coeficientes indeterminados; mínimo en Lagrange, intermedio en Newton.

  - *Coste de evaluación*: mínimo en coeficientes indeterminados (Algoritmo de Horner), bajo en Newton y alto en Lagrange.

  - *Coste de añadir nuevo nodo*: muy bajo en Newton, alto en coeficientes indeterminados y Lagrange.

  En vista de lo anterior, la forma de Newton parece la más recomendable, aunque en algunos casos también se emplea la forma de Lagrange.
]

#pagebreak()

== Cotas de error

#theorem[
  Supongamos que $f$ es una función con $N>=1$ derivadas continuas en un intervalo [a, b] y tal que $f^((N+1))$ existe en $(a, b)$.
  Sean $x_0, x_1, ..., x_N, thick N+1$ nodos en $[a, b]$ distintos dos a dos y $p$ el polinomio interpolador de Lagrange.
  Entonces dado $x in [a, b]$ existe $xi in I, thick I = (min(x_0, x_1, ..., x_n, x), max(x_0, x_1, ..., x_n, x))$ para el cual:

  $ f(x) - p(x) = ((x-x_0)(x-x_1)...(x-x_N))/((N+1)!) f^((N+1))(xi) $
]

#corollary[
  Si además de la hipótesis anterior suponemos $abs(f^((N+1)) (t)) <= K_(N+1), thick forall t in (a, b)$, entonces:

  $ abs(f(x) - p(x)) <= (abs(x-x_0) abs(x-x_1) ... abs(x-x_n))/((N+1)!) K_(N+1) $
]

== Diferencias divididas y derivadas

#theorem[
  Si $p$ es el polinomio interpolador de Lagrange de grado $N$ que interpola a $f$ en los $N+1$ nodos distintos dos a dos $x_0, x_1, ..., x_N$, entonces para cada $x$ distinto de los nodos donde $f$ esté definida se tiene:

  $ f(x) - p(x) = f[x_0, x_1, ..., x_N, x] (x-x_0) ... (x-x_N) $
]

#corollary[
  Sea $N$ un número no negativo y $x_0, x_1, ..., x_(N+1), thick N+2$ puntos distintos dos a dos en el intervalo $[a, b]$.
  Si $f$ es una función con $N$ derivadas continuas en $[a, b]$ y $f^((N+1))$ existe en $(a, b)$, entonces existe $xi in I, thick I = (min(x_0, ..., x_(N+1)), max(x_0, ..., x_(N+1)))$ para el que:


$ f[x_0, x_1, ..., x_(N+1)] = (f^((N+1)) (xi))/((N+1) !) $
]

#pagebreak()

== Convergencia de los polinomios de interpolación de Lagrange

#proposition(title: "Convergencia de los polinomios de interpolación de Lagrange")[
  Dada una función $f$ definida en un intervalo $[a, b]$, elegimos un punto $x_0^0$ e interpolamos en él por una constante $p_0$; después elegimos dos puntos distintos entre sí $x_0^1, x_1^1$ e interpolamos por una recta $p_1$.
  Continuando con este proceso, ¿será cierto que $lim_(N->oo) p_N(x) = f(x)$?
  La respuesta es, en general, *negativa*, con la conclusión de que incrementar el grado de los polinomios de interpolación en el problema de Lagrange no siempre es recomendable.
]

#emph-box[
  *Fenómeno de Runge*

  En 1900, el matemático Runge demostró que si se interpola la función $1\/(1+x^2)$, que posee derivadas continuas en todos los órdenes, en $N + 1$ abcisas equiespaciadas en el intervalo $[-5, 5]$ y se denota por $p_N$ su polinomio interpolador. 

Entonces cuando $N->oo, thick thick p_N(x)$ no converge al valor de $f(x)$ si $abs(x) > 3.6$.
]
