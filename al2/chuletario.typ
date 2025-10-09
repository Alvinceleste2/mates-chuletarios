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
  title: "Chuletario Álgebra II",
  author: "Álvaro Grande Blázquez",
  course: "2025 ~ 2026",
  watermark: "AGB",
)

= Repaso de teoría de cuerpos
== Estructuras algebraicas

#definition(title: "Operación binaria")[
  Sea $C$ un conjunto. Una *operación binaria* en $C$ es una aplicación:

  $ ast: & C times C & -> & thick med C \ & thick (a, b) &|-> & a*b $

  Además, se impone que al operar dos elementos de $C$, el resultado debe estar en $C$.
]

#definition(title: "Grupo")[
  Un *grupo* $(G, ast)$ es un conjunto con una operación binaria $ast$ tal que:
  
  - $ast$ es asociativa: $forall a, b, c in G, thick (a ast b) ast c = a ast (b ast c)$
  - Existe elemento neutro: $exists e in G | forall a in G, thick e ast a = a ast e = a$
  - Existe elemento inverso: $forall a in G thick exists a^(-1) in G | a ast a^(-1) = a^(-1) ast a = e$

El grupo es *conmutativo (abeliano)* si $forall a, b in G, thick a ast b = b ast a$.
]

#definition(title: "Anillo")[
  Un *anillo* $(A, ast, circle.stroked.tiny)$ es un conjunto $A$ con dos operaciones binarias $ast, circle.stroked.tiny$ tales que:

  - $(A, ast)$ es un grupo abeliano.
  - $circle.stroked.tiny$ es asociativa.
  - Se cumplen las leyes de distributividad:
    - $(a ast b) circle.stroked.tiny c = (a circle.stroked.tiny c) ast (b circle.stroked.tiny c)$
    - $a circle.stroked.tiny (b ast c) = (a circle.stroked.tiny b) ast (a circle.stroked.tiny c)$

  El anillo es *conmutativo* si $circle.stroked.tiny$ es conmutativa. \
  El anillo *tiene unidad* si existe un neutro para $circle.stroked.tiny$
]

#note-box[
  En este curso, "anillo" significará anillo conmutativo con unidad (salvo pocas excepciones)
]

#definition(title: "Cuerpo")[
  Un *cuerpo* $(K, ast, circle.stroked.tiny)$ es un conjunto $K$ con al menos dos elementos y dos operaciones binarias $ast, circle.stroked.tiny$ tales que:
  
  - $(K, ast, circle.stroked.tiny)$ es un anillo conmutativo con unidad.
  - Todo elemento $a in K$, $a != e$, tiene un inverso para $circle.stroked.tiny$.
]

#definition[
  Sea $(A, +, ·)$ un anillo. Entonces:

  - Un elemento $a in A$ es un *divisor de cero* si $a != 0$ y existe $b in A without {0}$ tal que $a · b = 0$.
  - Un elemento $a in A$ es una *unidad* si existe $b in A$ tal que $a · b = 1$. Decimos que $b = a^(-1)$ es su inverso.
  - El anillo $A$ es un dominio de integridad si $forall a, b in A, thick a · b = 0 => a = 0 or b = 0$, es decir, no hay divisores de 0.
]

#lemma[
  Todo cuerpo es un dominio de integridad.
]

#definition(title: "Anillo de polinomios")[
  Sea $A$ un anillo conmutativo.
  El *anillo de polinomios* $A[X]$ en una variable $x$ es el conjunto de expresiones de la forma:
  $ a_n x^n + a_(n-1) x^(n-1) + ... a_1 x + a_0, quad a_i in A $

  con la suma y el producto habituales.
]

== Ideales y cocientes
== Factorización en anillos de polinomios

= Extensiones de cuerpos
== Extensiones algebraicas
== Cuerpos finitos
== Grado de una extensión de cuerpos
== Polinomio mínimo
== Aplicación a las construcciones con regla y compás

= Extensiones de Galois
== El cuerpo de descomposición de un polinomio
== Clausura algebraica
