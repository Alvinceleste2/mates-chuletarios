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
  Entonces dado $x in [a, b]$ existe $xi in I, thick I = (min(x_0, x_1, ..., x_n, x), max(x_0, x_1, ..., x_n, x))$ para el cual:

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

  En 1900, el matemático Runge demostró que si se interpola la función $1\/(1+x^2)$, que posee derivadas continuas en todos los órdenes, en $N + 1$ abcisas equiespaciadas en el intervalo $[-5, 5]$ y se denota por $p_N$ su polinomio interpolador. 

Entonces cuando $N->oo, thick thick p_N(x)$ no converge al valor de $f(x)$ si $abs(x) > 3.6$.
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
  Siempre $f$ tenga derivada segunda acotada, si generamos una sucesión de particiones con diámetro $h$ tendiendo a 0 (para lo cual tendremos que incluir cada vez más puntos) tenemos garantizada la convergencia uniforme de la sucesión de interpolantes lineales a trozos.
  Esta convergencia será además *cuadrática*.
]

== Comparación con la interpolación polinómica de Lagrange

#proposition[
  Dada una partición $Delta$ y los valores de una función en los $N + 1$ nodos, podemos buscar el interpolante de Lagrange de grado $N$, $p$, o aproximarla por una funci

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

  $ abs(f(x) - h(x)) <= (5 h^4)/(384) K_4, quad x in [a, b] $

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

= Polinomios ortogonales

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

