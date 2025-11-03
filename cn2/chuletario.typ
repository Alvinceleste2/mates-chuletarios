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

#definition(title: "Problema de Lagrange")[
  Dados un entero no negativo $N$, $N+1$ puntos reales $x_0, x_1, ..., x_N$ distintos dos a dos y valores $f(x_0), f(x_1), ..., f(x_N)$ de una función, el *problema de interpolación de Lagrange* se basa en encontrar un polinomio de grado $N$ tal que:

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

== Comparación entre coeficientes indeterminados, Lagrange y Newton

#proposition[
  Hemos visto tres formas de construir el polinomio interpolador de Lagrange. Vamos a compararlas:

  - *Coste de construcción*: máximo en coeficientes indeterminados; mínimo en Lagrange, intermedio en Newton.

  - *Coste de evaluación*: mínimo en coeficientes indeterminados (Algoritmo de Horner), bajo en Newton y alto en Lagrange.

  - *Coste de añadir nuevo nodo*: muy bajo en Newton, alto en coeficientes indeterminados y Lagrange.

  En vista de lo anterior, la forma de Newton parece la más recomendable, aunque en algunos casos también se emplea la forma de Lagrange.
]

#pagebreak()

== Cotas de error

#theorem(title: "Error de interpolación de Lagrange")[
  Supongamos que $f$ es una función con $N>=1$ derivadas continuas en un intervalo [a, b] y tal que $f^((N+1))$ existe en $(a, b)$.
  Sean $x_0, x_1, ..., x_N, thick N+1$ nodos en $[a, b]$ distintos dos a dos y $p$ el polinomio interpolador de Lagrange.
  Entonces dado $x in [a, b]$ existe $xi in I$, #linebreak(justify: true) $I = (min(x_0, x_1, ..., x_n, x), max(x_0, x_1, ..., x_n, x))$ para el cual:

  $ f(x) - p(x) = ((x-x_0)(x-x_1)...(x-x_N))/((N+1)!) f^((N+1))(xi) $
]

#corollary[
  Si además de la hipótesis anterior suponemos $abs(f^((N+1)) (t)) <= K_(N+1), thick forall t in (a, b)$, entonces:

  $ abs(f(x) - p(x)) <= (abs(x-x_0) abs(x-x_1) ... abs(x-x_n))/((N+1)!) K_(N+1) $
]<cota-lagrange>

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

  En 1900, el matemático Runge demostró que si se interpola la función $1\/(1+x^2)$, que posee derivadas continuas en todos los órdenes, en $N + 1$ abcisas equiespaciadas en el intervalo $[-5, 5]$ y se denota por $p_N (x)$ su polinomio interpolador. 

Entonces cuando $N->oo, thick thick p_N (x)$ no converge al valor de $f(x)$ si $abs(x) > 3.6$.
]

= Interpolación de Taylor

== El problema de interpolación de Taylor

#definition(title: "Problema de interpolación de Taylor")[
  Dados un entero no negativo $N$, un punto $x_0$ de la recta y los valores $f(x_0), f'(x_0), ..., f^((N)) (x_0)$ de una función y sus $N$ primeras derivadas en $x_0$. El *problema de interpolación de Taylor* se basa en encontrar un polinomio de grado menor o igual que $N$ tal que $p(x_0) = f(x_0), thick p'(x_0) = f'(x_0), thick p^((N)) (x_0) = f^((N))(x_0)$.
]

#theorem[
  El problema de interpolación de Taylor tiene solución única.
  Al polinomio solución se le llama polinomio de Taylor de grado $N$ de $f$ en $x_0$.
]

#lemma(title: "Fórmula del polinomio de Taylor")[
  Construimos el polinomio de Taylor de grado $N$ de $f$ en $x_0$ de la siguiente manera:

  $ p(x) = f(x_0) + f'(x_0) (x- x_0) + (f''(x_0)) / 2! (x-x_0)^2 + ... + (f^((N)) (x_0)) / N! (x - x_0)^N $
]

== Notaciones de Landau

#definition[
  - Escribimos *$f = o(g)$* cuando $x-> x_0$ si para $x$ próximo a $x_0 thick x != x_0$, $f$ y $g$ están definidas, $g$ no se anula y $lim_(x->x_0) (f(x))/(g(x)) = 0$.

  - Escribimos *$f = O(g)$* cuando $x-> x_0$ si existe una constante $K > 0$ tal que para $x$ próximo a $x_0$, $f$ y $g$ están definidas y satisfacen $abs(f(x)) <= K abs(g(x))$.

Las notaciones de Landau también se usan cuando $x_0 = plus.minus oo$. Si $f_1 - f_2 = o(g)$ cuando $x -> x_0$ también se escribe $f_1 = f_2 + o(g)$. 
]

#pagebreak()

== Caracterización analítica del polinomio de Taylor

#theorem[
  Para $N>=1$, sea $f$ una función para la que se puede proponer el polinomio de Taylor, es decir, $N$ veces derivable en $x_0$. Entonces el polinomio de Taylor verifica:

  $ f(x) - p(x) = o((x - x_0)^N), quad x->x_0 $

  Además, $p$ es el único polinomio de grado $N$ que verifica esta propiedad.
]

== Cotas de error

#theorem(title: "Error en el polinomio de Taylor. Forma de Lagrange")[
  Sean $x, x_0$ dos números reales distintos y sea $f$ una función con $N$ derivadas continuas en el intervalo cerrado de extremos $x$ y $x_0$ al que llamaremos $overline(I)$.
  Supongamos además que existe $f^((N+1))$ en el intervalo abierto con los mismos extremos al que llamaremos $I$.
  Entonces, existe $xi in I$ tal que:

  $ f(x) - p(x) = (f^((N+1)) (xi))/((N+1)!) (x - x_0)^(N+1) $
]<error-lagrange>

#corollary[
  Si además de las hipótesis anteriores suponemos que $abs(f^((N+1)) (t)) <= K_(N+1), thick t in I$, entonces:

  $ abs(f(x) - p(x)) <= (abs(x-x_0)^(N+1) K_(N+1))/((N+1)!) $
]

#pagebreak()

#theorem(title: "Error en el polinomio de Taylor. Forma integral")[
Sean $x, x_0$ dos números reales distintos y sea $f$ con $N+1$ derivadas continuas en el intervalo $overline(I)$ del @error-lagrange. Entonces:

  $ f(x) - p(x) = 1/N! integral_(x_0)^x (x - s)^N f^((N+1)) (x) thick d s $
]

== Convergencia de la sucesión de los polinomios de Taylor

#proposition[
  Sean $p_0(x), p_1(x), ..., p_N (x)$ los polinomios de Taylor de grado $N$ de $f$ en $x_0$.
  Nos preguntamos si:

  $ f(x) = lim_(N->oo) p_N (x) = lim_(N->oo) sum_(n=0)^N (f^((n)) (x_0)) / (n!) (x-x_0)^n $
  Es decir, si $f(x)$ es la suma correspondiente a la serie de Taylor:

  $ f(x) = sum_(n=0)^oo (f^((n)) (x_0)) / (n!) (x - x_0)^n  $

  Podemos hacer los siguientes comentarios al respecto:

  - Se necesita una función $f$ con derivadas de todos los órdenes en $x_0$.

  - Puede que existan las derivadas pero que la serie no converja excepto en el punto $x_0$.

  - Aunque existan todas las derivadas y la serie converja puede ocurrir que la suma de la serie solo coincida con la función en el punto $x_0$.
]

= Interpolación polinómica a trozos

== Interpolación lineal a trozos

#definition[
  Dado un intervalo $[a, b]$ y una partición del mismo $Delta := a = x_0 < x_1 < ... < x_N = b$, denotamos por *$M_0^1(Delta)$* el espacio formado por todas las funciones continuas en $[a, b]$ que restringidas en cada intervalo $[x_(i-1), x_i], thick i = 1, ..., N$, son un polinomio de grado menor o igual que 1.
]

#definition[
  Si $s in M_0^1(Delta)$ decimos que $s$ es una *función lineal a trozos* (en la partición $Delta$).
  En los $x_i in Delta$ las funciones $s in M_0^1 (Delta)$ presentan saltos en la derivada.
]

== Funciones lineales a trozos como interpolantes

#definition(title: "Interpolante lineal a trozos")[
  Es obvio que dada una partición $Delta$ y dados los valores de una función $f(x_0), ..., f(x_N)$ en los nodos de la misma, existe una única función lineal a trozos, $s in M_0^1(Delta)$, tal que:

  $ s(x_0) = f(x_0), thick s(x_1) = f(x_1), thick ..., thick s(x_N) = f(x_N) $
  Llamaremos a esta función $s$ *interpolante lineal a trozos* de $f$ en la partición $Delta$.
]

#theorem(title: "Error de interpolación lineal a trozos")[
  Bajo las hipótesis anteriores y empleando el @cota-lagrange, podemos estimar el error de la interpolación lineal a trozos de la siguiente manera:

  $ abs(f(x) - s(x)) <= 1/8 h^2 K_2, quad x in [a, b] $

  Donde $h = max_i (x_i - x_(i-1))$ (es decir, $h = $ diámetro de la partición) y $K_2$ es una cota de la derivada segunda de $f$ en $[a, b]$.
]

#corollary(title: "Convergencia de la interpolación lineal a trozos")[
  Siempre que $f$ tenga derivada segunda acotada, si generamos una sucesión de particiones con diámetro $h$ tendiendo a 0 (para lo cual tendremos que incluir cada vez más puntos) tenemos garantizada la convergencia uniforme de la sucesión de interpolantes lineales a trozos.
  Esta convergencia será además *cuadrática*.
]

== Comparación con la interpolación polinómica de Lagrange

#proposition[
  Dada una partición $Delta$ y los valores de una función en los $N + 1$ nodos, podemos buscar el interpolante de Lagrange de grado $N$, $p$, o aproximarla por una función lineal a trozos $s$. Entonces tenemos lo siguiente:

  - *Coste de evaluación*: si $N$ es grande, el coste de evaluar $p$ es grande, mientras que el coste de evaluar $s$ no crece con $N$.
  - *Convergencia a $f$*: no está garantizada la convergencia de $p$ a la función $f$ mediante el aumento de $N$. Sin embargo, al refinar $Delta$ logramos que $s$ converja cuadráticamente a $f$, siempre que $f$ tenga derivada segunda acotada.
  - *Continuidad*: el polinomio $p$ es indefinidamente derivable mientras que $s$ es solo continuo, no derivable en los nodos de la partición.
]

== Funciones cuadráticas a trozos como interpolantes

#definition[
  Denotamos por *$M_0^2 (Delta)$* el conjunto de las funciones continuas en $[a, b]$ que restringidas a cada intervalo de la partición $[x_(i-1), x_i]$ coinciden con un polinomio de grado menor o igual que 2.
]

#definition[
  Si $q in M_0^2 (Delta)$ decimos que $q$ es una *función cuadrática a trozos* en la partición $Delta$.
  En los nodos $x_i in Delta$ las funciones $q in M_0^2 (Delta)$ presentan saltos en las derivadas primera y segunda.
]

#theorem(title: "Error de interpolación cuadrática a trozos")[
  Bajo las hipótesis anteriores, podemos estimar el error de la interpolación cuadrática a trozos de la siguiente manera:

  $ abs(f(x) - q(x)) <= sqrt(3)/216 h^3 K_3, quad x in [a, b] $

  Donde $h$ es el diámetro de la partición y $K_3$ es una cota de la derivada tercera de $f$ en $[a, b]$.
]

#corollary(title: "Convergencia de la interpolación cuadrática a trozos")[
  Al igual que en el caso lineal a trozos, tenemos convergencia de los interpolantes al refinar la partición.
  Esta vez, la convergencia será *cúbica*.
]

= Interpolación de Hermite

== Interpolación de Hermite

#definition(title: "Problema de interpolación de Hermite")[
  Dados $x_0, ..., x_r$ nodos con $0<=r<=N$, el *problema de interpolación de Hermite* se basa en encontrar un polinomio que reproduce a $f$ y sus $m_i$ primeras derivadas de forma que $sum_(i=0)^r (1 + m_i) = N + 1$. Más concretamente, buscamos $p$ de grado menor o igual que $N$ satisfaciendo:

#align(center)[
#table(
  columns: 4,
  rows: 4,
  inset: 10pt,
  stroke: none,
  align: horizon,
  $ p(x_0) = f(x_0), $, $ p'(x_0) = f'(x_0), $, $ ... $, $ p^((m_0)) (x_0) = f^((m_0)) (x_0), $,
  $ p(x_1) = f(x_1), $, $ p'(x_1) = f'(x_1), $, $ ... $, $ p^((m_1)) (x_1) = f^((m_1)) (x_1), $,
  $ ... $, $ ... $, $ ... $, $ ... $,
  $ p(x_r) = f(x_r), $, $ p'(x_r) = f'(x_r), $, $ ... $, $ p^((m_r)) (x_r) = f^((m_r)) (x_r) $,
)
]

  Este problema es una generalización de la interpolación de Lagrange donde $r = N$ y $m_0 = m_1 = ... = m_r = 0$.
  También es una generalización de la interpolación de Taylor, donde $r = 0$ y $m_0 = N$.
]

#lemma(title: "Construcción de polinomio interpolador de Hermite")[
  Sea la siguiente base:

  $
  {1, (x-x_0), ..., (x-x_0)^(m_0), (x-x_0)^(m_0 + 1), (x-x_0)^(m_0 + 1) (x-x_1), ..., \
  (x-x_0)^(m_0+1)(x-x_1)^(m_1), ..., (x-x_0)^(m_0 + 1) (x-x_1)^(m_1 + 1) ... (x-x_(r-1))^(m_(r-1) + 1), ..., \ 
  (x-x_0)^(m_0+1)(x-x_1)^(m_1+1)...(x-x_(r-1))^(m_(r-1)+1)(x-x_r)^(m_r) }
  $

  El polinomio interpolador de Hermite se escribe:

  $ p(x) = f(x_0) + f'(x_0)(x-x_0) + ... + (f^((m_0)) (x_0)) / (m_0 !)(x-x_0)^(m_0) + \
  + thick c_(m_0+1)(x-x_0)^(m_0+1) + c_(m_0+2)(x-x_0)^((m_0+1))(x-x_1)... $
]

#theorem[
  El problema de interpolación de Hermite tiene solución única.
]

#theorem(title: "Error de interpolación de Hermite")[
  Sea $f$ de clase $cal(C)^N$ en un intervalo $[a, b]$ y de modo que existe $f^((N+1))$ en $(a, b)$.
  Entonces para cada $x in [a, b]$ existe $xi in I, thick I = (min(x_0, x_1, ..., x_n, x), max(x_0, x_1, ..., x_n, x))$ para el cual:

  $ f(x) - p(x) = ((x-x_0)^(m_0+1)...(x-x_r)^(m_r+1))/((N+1)!) f^((N+1)) (xi) $
]

#proposition(title: "Diferencias divididas en Hermite")[
  Podemos extender la idea de las diferencias divididas al caso en el que tengamos argumentos repetidos. Para ello, imponemos las siguientes normas:

  - Las diferencias divididas no dependen del orden en que se escriban sus argumentos.
  - Cuando todos los argumentos son iguales, la diferencia dividida $i$-ésima se define como:

  $ f[x_0, x_0, ..., x_0] = (f^(i) (x_0))/(i!) $

  - Si entre los argumentos hay dos con valores distintos, que según la primera norma, podemos suponer que son el primero y el último, se aplica la fórmula:

  $ f[x_0, ..., x_i] = (f[x_1, ..., x_i] - f[x_0, ..., x_(i-1)]) / (x_i - x_0) $
]

#lemma[
  Dada una función de clase $cal(C)^i$, su diferencia dividida $i$-ésima es una función continua de sus $i+1$ variables. Por eso, se verifica por ejemplo que:

  $ f[x_0, x_0] = lim_(x_1->x_0) f[x_0, x_1] = lim_(x_1 -> x_0) (f(x_1) - f(x_0))/ (x_1 - x_0) = f'(x_0) $
]

== Interpolantes cúbicos de Hermite a trozos

#definition[
  Dade un intervalo $[a, b]$ y una partición del mismo $Delta := a = x_0 < x_1 < ... < x_N = b$, denotaremos por *$M_1^3 (Delta)$* el espacio de las funciones reales de clase $cal(C)^1[a, b]$ que, restringidas a cada subintervalo de la partición $(x_(i-1), x_i), thick i = 1, ..., N$, son un polinomio de grado menor o igual que 3.
]

#lemma(title: "Construcción del interpolante cúbico de Hermite a trozos")[
  Sea la siguiente base:

  $
  phi.alt_i (x_j) = delta_(i, j), quad phi.alt'_i (x_j) = 0, quad quad & 0 <= i <= N, \
  theta_i (x_j) = 0, quad theta'_i (x_j) = delta_(i, j), quad quad & 0<= i <= N
  $

  El interpolante cúbico de Hermite a trozos se escribe:

  $ h(x) = sum_(i=0)^N (h(x_i)phi.alt_i (x) + h'(x_i)theta_i (x)) $
]

== Splines cúbicos

#definition(title: "Splines")[
  Definimos *$M_2^3 (Delta)$*, llamados *splines*, como el espacio de funciones de clase $cal(C)^2[a, b]$ y cúbicas a trozos.
]

#theorem[
  Dada $f$ continua en $[a, b]$ y derivable en $a$ y $b$, existe un único spline cúbico $h in M_2^3 (Delta)$ tal que $h(x_i) = f(x_i), thick i=0, ..., N, thick h'(a) = f'(a), thick h'(b) = f'(b)$.
  
  A este spline se le llama *interpolante completo de $f$*.
  Para calcular $h$ se debe resolver primero el sistema siguiente (@sistema-hermite) para encontrar los valores $h'(x_i)$ en los nodos interiores y después construir el spline en cada intervalo usando los valores del mismo y su derivada en los extremos del intervalo.
]

#lemma(title: "Sistema de ecuaciones para obtención de valores del spline")[
$
  mat(
  2/(x_1-x_0) + 2/(x_2-x_1), 1/(x_2-x_1), ..., ..., 0;
  1/(x_2-x_1), 2/(x_2-x_1) + 2/(x_3-x_2), 1/(x_3-x_2) ,..., 0;
  dots.v, dots.v, dots.v, dots.down, dots.v;
  0, 0, 0, 1/(x_(N-1)-x_(N-2)), 2/(x_(N-1)-x_(N-2)) + 2/(x_N - x_(N-1));
  ) 
  mat(
  h'(x_1);
    h'(x_2);
    dots.v;
    h'(x_(N-1));
  ) \ \ \

  =
  mat(
    (3(h(x_2)-h(x_1)))/(x_2-x_1)^2 + (3(h(x_1)-h(x_0)))/(x_1-x_0)^2 - (h'(x_0))/(x_1-x_0);
    (3(h(x_3) - h(x_2)))/(x_3-x_2)^2 + (3(h(x_2) - h(x_1)))/(x_2 - x_1)^2;
    dots.v;
    (3(h(x_N) - h(x_(N-1))))/(x_N - x_(N-1))^2 + (3(h(x_(N-1))- h(x_(N-2))))/(x_(N-1) - x_(N-2))^2 - (h'(x_N))/(x_N - x_(N-1));
  )
$
]<sistema-hermite>

#theorem[
  Para el spline completo $h$ de $f$ tenemos:

  $ abs(f(x) - h(x)) <= 5/(384) h^4 K_4, quad x in [a, b] $

  Donde $K_4$ es una cota de la derivada cuarta de $f$ en el intervalo $[a, b]$.
]

= Polinomios de Chebyshev

== Polinomios de Chebyshev

#definition(title: "Norma infinito")[
  Dada una función $v(x)$ acotada definida en $[a, b]$ definimos su *norma infinito* como:

  $ ||v||_oo = max_(a <= x <= b) abs(v(x)) $
]

#theorem[
  Para cada entero $n >= 0$ existe un único polinomio $T_n$, llamado *enésimo polinomio de Chebyshev*, tal que para cada $theta$ real se cumple que:

  $ T_n (cos(theta)) = cos(n theta) $

  El polinomio $T_n$ tiene grado exactamente $n$. Si $n >= 1$, el coeficiente de $x^n$ es $2^(n-1)$. Además, para $n>=2$ se verifica:

  $ T_n (x) = 2x T_(n-1) (x) - T_(n-2) (x) $
]

#theorem[
  Los $n$ ceros de $T_n$ son los puntos $eta_k^n = cos((2k - 1) pi/(2n))$, para $k = 1, ..., n$. Se verifica que:

  $ -1 <= T_n (x) <= 1, quad -1 <= x <= 1 $

  Los valores extremos 1 y -1 se alcanzan en los puntos $xi_k^n = cos((2k)pi/(2n))$, para $k = 0, ..., n$ y en ellos $T_n (xi_k^n) = (-1)^k$.
]

#theorem[
  El enésimo polinomio de Chebyshev $T_n (x)$ tiene norma infinito en $[-1, 1]$ no mayor que cualquier otro polinomio de grado $n$ con su mismo coeficiente director.
]

#theorem[
  El polinomio $T_n (x) \/ 2^(n-1)$ tiene norma infinito en $[-1, 1]$ no mayor que cualquier otro polinomio de grado $n$ y coeficiente director 1.
]

#theorem[
  La norma $||W||_oo$ con $W(x) = (x-x_0)(x-x_1)...(x-x_N)$ es mínima en $[-1, 1]$ si $x_0, ..., x_N$ se escogen como los $N+1$ ceros del polinomio de Chebyshev $T_(N+1)$.
]

== Acondicionamiento de las diversas representaciones de un polinomio

#lemma[
  Muchas veces se emplean los polinomios de Chebyshev como base para representar polinomios de grado $<= n$ como combinación lineal $a_0 T_0 + ... + a_n T_n$.
]

#definition(title: "Acondicionamiento de una base")[
  Sea $cal(B)$ una base. Se dice que $cal(B)$ está *bien condicionada* cuando pequeños errores relativos en los coeficientes conducen a pequeños errores relativos en los valores. Por el contrarior, $cal(B)$ se dice *mal condicionada* cuando pequeños errores relativos en los coeficientes condicen a errores relativos mucho mayores en los valores del polinomio. cuando pequeños errores relativos en los coeficientes condicen a errores relativos mucho mayores en los valores del polinomio.
]

#proposition[
  - La base de monomios es muy mal acondicionada si se trabaja en un intervalo $[a, b]$ cuya longitud sea pequeña comparada con la magnitud de $a$ o $b$. En esas situaciones es mejor trabajar con una base de potencias escaladas $[(x-a)/(b-a)]^k$.
  - Para polinomios de grado alto, la base de anterior es también mal acondicionada.
  - La base de polinomios de Chebyshev presenta buen acondicionamiento.
  - La base de polinomios de Lagrange basados en los ceros del polinomio de Chebyshev es (casi) la mejor acondicionada posible. 
]

= Polinomios ortogonales <orto-pol>

== Aproximación en un espacio con un producto interno

#definition(title: "Función peso")[
  Dado un intervalo de la recta real $(a, b)$, acotado o no, una *función peso* $w$ en $(a, b)$ es una función real definida en $(a, b)$, continua, positiva excepto quizás en un conjunto finito de puntos (en los que es nula) y tal que para cada $n=0, 1, 2, ...$ las integrales:

  $ integral_a^b x^n w(x) thick d x $

  existen.
]

#definition(title: "Norma de una función peso")[
  Sean $w$ una función peso, $f$ una función y $p$ su interpolante de grado menor o igual que $n$. Definimos $||f - p||_w$, la *norma $w$* como:

  $ ||f - p||_w = (integral_a^b |f(x) - p(x)|^2 w(x) thick d x)^(1/2) $

  En particular, buscamos que las desviaciones $f(x) - p(x)$ correspondientes a los $x$ en los que $w$ es mayor contribuyan más que las correspondientes a los $x$ en los que $w$ es pequeño.
]

#proposition[
  Sea $X$ un espacio vectorial normado con norma $||dot||_X$, $S$ un subconjunto de $X$ no vacío y compacto y $f in X$. Entonces $f$ tiene al menos una mejor aproximación por elementos de $S$ en la norma $||dot||_X$.
]

#proposition[
  Sea $X$ un espacio vectorial normado con norma $||dot||_X$ y $S$ un subespacio vectorial de dimensión finita y $f in X$, entonces $f$ tiene al menor una mejor aproximación por elementos de $S$ en la norma $||dot||_X$.
]<prop-2>

#theorem[
  Sea $X$ un espacio vectorial normado con norma $||dot||_X$ cuya norma deriva de un producto interno $(dot, dot)_X$ y sea $S$ un subespacio vectorial de $X$.
  Si existe $p^*$ aproximación óptima a $f$ por elementos de $X$, entonces es única y satisface:

  $ (f - p^*, p)_X = 0, quad forall p in S wide (ast) $

  Recíprocamente, si un elemento $p^* in S$ satisface $(ast)$, entonces es la mejor aproximación.
]<theorem-1>

#lemma[
  Observamos que si el subespacio $S$ es de dimensión finita, la @prop-2 garantiza la existencia de la mejor aproximación y el @theorem-1 la unicidad y caracterización de la misma con la propiedad $(ast)$.
  La mejor aproximación es en este caso la *proyección ortogonal* sobre el subespacio $S$.
]

== Polinomios ortogonales

#definition(title: "Sucesión de polinomios ortogonales")[
  Dada una función peso $w$ en $(a, b)$, en lo sucesivo consideramos el espacio vectorial \ $X = L_w^2(a, b)$ con norma $||dot||_X = ||dot||_w$. Una *sucesión de polinomios ortogonales* ${Q_n}_(n=0)^oo$ es una sucesión en la que $Q_n$ es un polinomio de grado exactamente $n$ y además $(Q_n, Q_m)_w = 0$ si $n!=m; thick n, thick m = 0, 1, ...$.
]

#lemma[
  Notemos que, fijada $w$, si ${Q_n}_(n=0)^oo$ y ${R_n}_(n=0)^oo$ son dos sucesiones de polinomios ortogonales, entonces $Q_n = alpha_n R_n, thick n=0, 1, 2, ...$ donde $alpha_n$ es un número real no nulo.
]

#theorem[
  Si ${Q_n}_(n=0)^oo$ es una sucesión de polinomios ortogonales, entonces existen constantes $c_n, thick a_n, thick b_n$ tales que:

  $ Q_n(x) = (c_n x - a_n) Q_(n-1) (x) - b_n Q_(n-2) (x), quad n = 2, 3, 4,... $

  Recíprocamente, definiendo:

  $
  Q_0 (x) = 1, \
  Q_q(x) = x - a_1, \
  a_n = ((x Q_(n-1), Q_(n-1))_w)/(Q_(n-1), Q_(n-1))_w, quad n = 1, 2, 3, ..., \
  b_n = ((x Q_(n-1), Q_(n-2))_w)/(Q_(n-2), Q_(n-2))_w, quad n = 2, 3, ..., \
  Q_n = (x - a_n) Q_(n-1) - b_n Q_(n-2), quad n = 2, 3, ...,
  $

  se genera la sucesión de polinomios ortogonales mónicos.
]

#theorem[
  Si ${Q_n}$ es una sucesión de polinomios ortogonales y $f in L_w^2 (a, b) inter C(a, b)$ es ortogonal a $Q_0, ..., Q_(n-1)$, entonces $f$ es idénticamente nula o hay $n$ puntos $r_i$ en $(a, b)$ en los que $f$ cambia de signo (es decir, hay un entorno de $r_i$ en el que $f > 0$ para $x < r_i$ y $f < 0$ para $x > r_i$, o bien $f<0$ para $x<r_i$ y $f>0$ para $x > r_i$)
]

#corollary[
  El polinomio $Q_n$ tiene $n$ raíces reales y simples en el intervalo $(a, b)$.
]

#pagebreak()

== Algunos polinomios ortogonales de interés

#lemma[
  - *Polinomios de Chebyshev*.
  Se definen por $T_n(cos(theta)) = cos(n theta)$. Son ortogonales en $(-1, 1)$ para la función peso:

  $ w(x) = 1/sqrt(1-x^2) $

  La mejor aproxumación a $f in L_w^2(a, b)$ por polinomios de grado menor o igual que $n$ se puede escribir como:

  $ p^* (x) = sum_(j=0)^n a_n T_j(x) $

  $ a_0 = 1/pi integral_(-1)^1 f (x) (d x)/sqrt(1-x^2), quad a_j = 2/pi integral_(-1)^1 f(x) T_j(x) (d x)/sqrt(1-x^2), quad n = 0, 1, 2, ... $

  - *Polinomios de Legendre*.

  Son ortogonales en $(-1, 1)$ para $w(x) = 1$ y se definen por:

  $ P_n(x) = 1/(2^n n!) (d^n)/(d x^n) (x^2 - 1)^n, quad n=0, 1, 2,... $

  - *Polinomios de Laguerre*.

  Son ortogonales en $(0, oo)$ para el peso $e^(-x)$ y se definen por:

  $ L_n(x) = e^x/n! d^n/(d x^n) (x^n e^(-x)), quad n = 0, 1, 2, ... $

  - *Polinomios de Hermite*.

  Son ortogonales en $(-oo, oo)$ para el peso $exp(-x^2)$ y se definen por:

  $ H_n(x) = (-1)^n e^x^2 d^n / (d x^n) exp(-x^2), quad n = 0, 1, 2, ... $
]

= Convergencia de las mejores aproximaciones

== Convergencia de las mejores aproximaciones polinómicas en $cal(C)[a, b]$

#theorem(title: "Teorema de Weierstrass")[
  Si $f$ es una función real continua en un intervalo compacto $[a, b]$, dado $epsilon > 0$ existe un polinomio $P$ tal que $abs(f(x) - P(x)) <= epsilon $ para cada $x$ en $[a, b]$.
]

#definition(title: "Polinomios de Bernstein")[
  Para $n = 1, 2, ...$ se define el $n$-ésimo polinomio de Bernstein $B_n$ (relativo a $f$) mediante la fórmula:

  $ B_n(x) = sum_(k=0)^n binom(n, k) x^k (1-x)^(n-k) f(k slash n) $
]

== Convergencia de los desarrollos ortogonales

#lemma[
  Supongamos que $X$ es uno de los espacios $L_w^2(a, b)$ considerados en la @orto-pol y que $S_n$ = $PP^n$.
  Si tomamos una sucesión de polinomios ortogonales ${Q_n}_(n=0)^oo$ en $L_w^2(a, b)$, la mejor aproximación $p_n$ a $f in L_w^2$ por polinomios de $PP^n$ se representa explícitamente como:

  $ p_n = sum_(i=0)^n ((f_i, Q_i)_w/(Q_i, Q_i)_w Q_i) $

  Por tanto, la cuestión de si $p_n -> f$ en $L_w^2(a, b)$ se reduce a examinar si:

  $ f = sum_(i=0)^oo (((f_i, Q_i)_w) / (Q_i, Q_i)_w Q_i) $

  donde la suma de la serie se entiende en el sentido de la norma de $L_w^2(a, b)$.
]

#definition[
  Cuando lo anterior es cierto, se dice que se ha *desarrollado* $f$ en serie de polinomios ortogonales.
]

#theorem[
  Si $f in cal(C)([-1, 1])$, entonces su desarrollo de Chebyshev converge a $f$ en la norma de $L_w^2$:

  $ w(x) = 1/(sqrt(1-x^2)) $
]

#theorem[
  Si $f in cal(C)^2([-1, 1])$, su desarrollo en serie de Chebyshev converge uniformemente hacia $f$.
]

= Cuadratura numérica

== Introducción

#definition(title: "Cuadratura")[
  Sea $f$ una función integrable en un intervalo acotado $(a, b)$. El cálculo aproximado de su integral, $integral_a^b f(x) d x$, se denomina *cuadratura*.
]

== Reglas de cuadratura

#definition(title: "Reglas de cuadratura")[
  Las *reglas de cuadratura* suelen estar formadas por una combinación lineal de valores nodales de la función $f$:

  $ integral_a^b f(x) d x approx I_(N+1) (f) = alpha_0 f(x_0) + alpha_1 f (x_1) + ... + alpha_N f(x_N) $

  Fijados $N$ y los valores de $alpha_i$ y $x_i, thick i = 0, ..., N$ la expresión anterior nos da una aproximación al valor exacto de la integral.
  Los $x_i$ se llaman abcisas o *nodos* de la regla de cuadratura, suponemos que son distintos dos a dos.
  Los nodos suelen pertenecer al intervalo $[a, b]$ pero no es imprescindible.
  Los $alpha_i$ se llaman *pesos* de la regla de cuadratura.
]

#lemma(title: "Algunas reglas de cuadratura sencillas")[
  - Regla del rectángulo $arrow$ $ wide thick thick thick I^R (f) = (b-a) f(a)$

  - Regla del punto medio $arrow$ $ wide I^(P M) (f) = (b-a) f(c), thick thick c=(a+b)/2$

  - Regla de los trapecios $arrow$ $ wide thick I^T (f) = (b-a)/2 f(a) + (b-a)/2 f(b)$

  - Regla de Simpson $arrow$ $ wide wide I^S (f) = (b-a)/6 f(a) + (4(b-a))/6 f(c) + (b-a)/6 f(b), thick thick c = (a+b)/2$
]

#pagebreak(weak: true)

#definition(title: "Grado de exactitud de las reglas de cuadratura")[
  Una regla de cuadratura tiene *grado de exactitud* $M >= 0$ si calcula exactamente la integral de cada polinomio de grado menor o igual que $M$ pero no calcula exactamente la integral de todos los polinomios de grado $M+1$.
  Es decir, $I(f) = I_(N+1) (f)$, para todo $f$ polinomio de grado hasta $M$.
]

#lemma(title: "Grados de exactitud de algunas reglas de cuadratura")[
  - Regla del rectángulo $arrow$ grado de exactitud = *0*
  - Regla del punto medio $arrow$ grado de exactitud = *1*
  - Regla del trapecio $arrow$ grado de exactitud = *1*
  - Regla del Simpson $arrow$ grado de exactitud = *3*
]

== Obtención de reglas de cuadratura

#proposition(title: "Método interpolatorio")[
  Consiste en sustituir el integrando $f$ por el polinomio interpolador de Lagrange de grado $N$, $p$, que coincide con $f$ en los nodos $x_i, thick i = 0, ..., N$.

  $ integral _a^b f(x) d x approx I_(N+1) (f) = integral_a^b p(x) d x = f(x_0) integral_a^b l_0(x) d x + ... + f(x_N) integral_a^b l_N (x) d x $

  Luego:

  $ I_N (f) = sum_(i=0)^N alpha_i f(x_i) "donde" alpha_i = integral_a^b l_i (x) d x $

  La regla obtenida por este procedimiento se llama *regla interpolatoria*.
]

#theorem[
  Dados $N >= 0$ y $N+1$ nodos $x_i$ distintos dos a dos, la correspondiente regla de cuadratura interpolatoria tiene grado de precisión al menos $N$.
]

#pagebreak(weak: true)

#proposition(title: "Método de coeficientes indeterminados")[
  Este método se basa en observar que la regla de cuadratura tiene grado de precisión $N$ si y solo si $I_(N+1) (f) = I(f)$ para $f(x) = 1, x, ..., x^N$. Imponiendo estas condiciones obtenemos el sistema:

  $
  alpha_0 + alpha-1 + ... alpha_N = (b-a), \
  alpha_0 x_0 + alpha_1 x_1 + ... + alpha_N x_N = (b^2 - a^2)/2, \
  dots.v \
  alpha_0 x_0^N + alpha_1 x_1^N + ... alpha_N x_N^N = (b^(N+1) - a^(N+1))/(N+1)
  $

  Observemos que el anterior es un sistema de $N+1$ ecuaciones con $N+1$ incógnitas, los $alpha_i$, que tiene por matriz la matriz de Vandermonde, que sabemos tiene determinante distinto de cero si y solo si los nodos son distintos dos a dos.
  Por tanto, existe una única solución que nos da la regla de cuadratura con grado de precisión al menos $N$.
]

#theorem[
  Dados $N>=0$ y $N+1$ nodos distintos dos a dos existe una única regla de cuadratura de grado de precisión al menos $N$.
  Los pesos de la regla se pueden calcular resolviendo el sistema anterior.
]

#proposition(title: "Método del desarrollo de Taylor")[
  En general, para aplicar el método del desarrollo de Taylor seguiremos los siguientes pasos:

  + Escoger un punto para hacer el desarrollo de Taylor. Puede ser uno de los nodos o cualquier punto que conduzca a simplificar los cálculos, en ocasiones $(a+b)/2$.

  + Desarrollar los valores $f(x_i)$ en desarrollos de Taylor en torno al punto del apartado anterior.

  + Desarrollar el integrando $f$ en torno al mismo punto.

  + Imponer que coincidan el mayor número de términos posibles en ambos desarrollos.
]

#proposition(title: "Error en las fórmulas de cuadratura")[
  Se pueden probar las siguientes cotas de error para las fórmulas más conocidas:

  - Regla del rectángulo $arrow$ Si $f in cal(C)^1 [a, b]$ entonces existe $eta in [a, b]$ tal que 
  $ E^R (f) = (b-a)^2/2 f'(eta) $

  - Regla del punto medio $arrow$ Si $f in cal(C)^2 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ E^(P M) (f) = (b-a)^3/24 f'''(eta) $

  - Regla de los trapecios $arrow$ Si $f in cal(C)^2 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ E^(T) (f) = -(b-a)^3/12 f''(eta) $

  - Regla de Simpson $arrow$ Si $f in cal(C)^4 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ E^(S) (f) = -(b-a)^5/2880 f^((4))(eta) $
]

#lemma[
  Sean $alpha$ y $g$ funciones reales en $[a, b]$ con $alpha >= 0$ y $g$ continua.
  Supongamos que #linebreak(justify: true) $A = integral_a^b alpha(x) d x != 0$ y que existe $integral_a^b g(x) alpha(x) d x$ entonces existe $eta in [a, b]$ tal que:

  $ integral_a^b g(x) alpha(x) d x = g(eta) integral_a^b alpha(x) d x $
]

#pagebreak(weak: true)

== Reglas de cuadratura compuestas

#definition(title: "Reglas de cuadratura compuestas")[
  Sea $Delta := a = x_0 < x_1 < ... < x_N = b$, podemos escribir:
  $ integral_a^b f(x) d x = integral_(x_0)^(x_1) f(x) d x + ... + integral_(x_(N-1))^(x_N) f(x) d x $
]

#lemma(title: "Algunas reglas de cuadratura compuestas")[
  - Regla del rectángulo:
  $ I^(R C) (f) = (x_1 - x_0) f(x_0) +(x_2 - x_1) f(x_1) + ... + (x_N - x_(N-1)) f(x_(N-1)) $

  - Regla del punto medio:
  $ I^(P M C) (f) = (x_1 - x_0) f(x_(1 slash 2)) + (x_2 - x_1) f(x_(3 slash 2)) + ... + (x_N - x_(N-1)) f(x_(N-1 slash 2)) $

  - Regla del trapecio:
  $
  I^(T C) (f) = (x_1 - x_0)/2 f(x_0) + (x_1 - x_0)/2 f(x_1) + (x_2 - x_1)/2 f(x_1) + (x_2 - x_1)/2 f(x_2) + ...\
   ... + (x_N - x_(N-1))/2 f(x_(N-1)) + (x_N - x_(N-1))/2 f(x_N) = \
  = sum_(i=1)^N (x_i-x_(i-1))/2 [f(x_(i-1)) + f(x_i))]
  $

  - Regla de Simpson 
  $ I^(S C) (f) = (x_1 - x_0)/6 f(x_0) + (4(x_1 - x_0))/6 f(x_(1 slash 2)) + (x_1 - x_0)/6 f(x_1) + ... \
  ... +(x_N - x_(N-1))/6 f(x_(N-1)) + (4 (x_N - x_(N-1)))/6 f(x_(N-1 slash 2)) + (x_N - x_(N-1))/6 f(x_N) = \
  = sum_(i=1)^N (x_i - x_(i-1))/6 [f(x_(i-1)) + 4 f((x_(i-1) + x_i)/2) + f(x_i)] $
]

#lemma[
  Sea $g$ una función continua en $[a, b]$, $alpha_i >= 0, thick i = 1, ..., N$, no todos nulos, y $eta_i in [a, b], thick i = 1, ..., N$.
  Entonces existe $eta in [a, b]$ tal que:

  $ alpha_1 g(eta_1) + alpha_2 g(eta_2) + ... + alpha_N(eta_N) = (alpha_1 + ... + alpha_N)g(eta) $
]<lema-error-comp>

#proposition(title: "Error en las fórmulas de cuadratura compuestas")[
  Empleando el @lema-error-comp obtenemos las siguientes cotas de error para las reglas compuestas. 
  Sean $h = max_(1<=i<=N)(x_i - x_(i-1))$ y $K_i$ una cota para $f^((i))$ en $[a, b]$:

  - Regla del rectángulo compuesta $arrow$ Si $f in cal(C)^1 [a, b]$ entonces existe $eta in [a, b]$ tal que 
  $ abs(E^(R C) (f)) = abs(1/2[(x_1 - x_0)^2 + ... + (x_N - x_(N-1)^2)] f'(eta)) <= 1/2 h (b-a) K_1 $

  - Regla del punto medio compuesta $arrow$ Si $f in cal(C)^2 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ abs(E^(P M C) (f)) = abs(1/24 [(x_1 - x_0)^3 + ... + (x_N - x_(N-1))^3] f''(eta)) <= 1/24 h^2(b-a) K_2 $

  - Regla de los trapecios compuesta $arrow$ Si $f in cal(C)^2 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ abs(E^(T C) (f)) = abs(-1/12 [(x_1 - x_0)^3 + ... (x_N - x_(N-1))^3] f''(eta)) <= 1/12 h^2 (b-a) K_2 $

  - Regla de Simpson compuesta $arrow$ Si $f in cal(C)^4 [a, b]$ entonces existe $eta in [a, b]$ tal que 

  $ abs(E^(S C)) <= 1/2880 h^4 (b-a) K_4 $
]

#note-box(title: "Relación con la interpolación polinómica a trozos")[
  - La regla de los trapecios compuesta se obtiene sustituyendo $f$ por su interpolante lineal a trozos en los nodos $x_0, x_1, ..., x_N$.

  - La regla de Simpson compuesta se obtiene sustituyendo $f$ por su interpolante cuadrático a trozos en los nodos $x_0, x_1, ..., x_N$ y los puntos medios.
]

#pagebreak(weak: true)

== Cuadratura Gaussiana

#definition(title: "Producto interno de dos funciones")[
  - Dado un intervalo $(a, b)$ y una función (que llamamos función peso) $w(x)$ definida en $(a, b)$ con $w(x)$ positiva excepto tal vez en un número finito de puntos donde es nula.
    Definimos el producto interno de dos funciones de cuadrado integrable respecto al peso $w(x)$ como:

    $ (f, g)_w = integral_a^b f(x) g(x) w(x) d x $

  - Al espacio de funciones de cuadrado integrable respecto al peso $w(x)$ lo denotaremos por $L_w^2(a, b)$.
    Las funciones peso en $(a, b)$ se definen de modo que exista $integral_a^b x^n w(x) d x, thick thick forall n$.

  - Dada una función peso en $(a, b)$ existe una familia de polinomios ortogonales en $(a, b)$ respecto a esa función peso:

    $ {q_0, q_1, ..., q_n, ...} $

    que verifican:

    - El polinomio $q_n$ tiene grado exactamente $n$.
    - $(q_n, q_m)_w = 0$ si $n!=m$.
    - Los polinomios ortogonales son únicos (salvo una constante) y se pueden generar por recurrencia.
]

#lemma[
  La regla gaussiana se obtiene tomando $x_0, x_1, ..., x_N$ los ceros del polinomio de Legendre de grado $N+1$ en el intervalo $(a, b)$, que sabemos tiene $N+1$ raíces reales y distintas.
]

#theorem[
  Una regla de cuadratura gaussiana puede tener a lo sumo grado de precisión $2N+1$.
  Este grado se alcanza cuando los nodos $x_i$ son las raíces del polinomio de grado $N+1$ ortogonal a los de grado $N$ en $[a, b]$ respecto al peso $1$.
]

#theorem[
  Los coeficientes $alpha_j, thick j = 0, ..., N$ de la regla gaussiana de $N+1$ nodos son todos positivos.
]
