
#import "../semantics.typ": *
#import "@preview/theorion:0.3.3": *
#import cosmos.fancy: *
#import "@preview/quick-maths:0.2.1": shorthands
#set text(lang: "en")
#show: show-theorion

== Logic
=== Propositional Logic

#definition(title: "Proposition")[
  A #def(<prop>)[proposition] is a statement that can be assigned a truth value.
]
#names(<prop>, plural: true, "proposition", "statement")

#definition(title: "Tautology")[
  A #def(<tautology>)[tautology] is a #n[proposition] that is always true. Let $dv(P)$ be a #n[proposition], then we denote "$rP$ is a tautology" as $tack.r dv(P)$.
]
#names(<tautology>, plural: true, "tautology", "truth")
#names(<tautology>, "true", "holds", "hold")

#let holds = $#lk(<tautology>, math.tack.r)$
==== Implication
#definition(title: "Implication")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<imp>)[implication] $rP arrow.double rQ$ to be #n[true], one needs a derivation of $holds rQ$ from $holds rP$. 

  In particular, this yields us #def(<imp.modus-ponens>)[modus ponens]: from $holds rP$ and $holds rP arrow.double rQ$, it follows that $holds rQ$.
]
#names(<imp>, "implication", "implications", "implies", "imply", "if", "then")
#names(<imp.modus-ponens>, "modus ponens")


#let imp = $#lk(<imp>, math.arrow.double)$

#remark(title: "Right associativity of implication")[
  For #n[propositions] $dv(P), dv(Q), dv(R)$, we write
  $rP imp rQ imp rR$ for $rP imp (rQ imp rR)$.
]<imp.right-assoc>

#remark(title: "Proving implications")[
  To prove an implication $dv(P) imp dv(Q)$, we usually start our proofs with a sentence along the lines of "Assume $rP$", or, if $rP$ contains a free variable $dv(x)$, "Let $rv(x)$ be $rP$". In the rest of the proof, we are free to use that assumption, as long as we finally show $rQ$.
]

#proposition(title: "Implication basics")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following always #n[hold]: 
  / Reflexivity: $rP imp rP$, <imp.refl>
  / Transitivity: $(rQ imp rR) imp (rP imp rQ) imp rP imp rR$, <imp.trans>
  / Contraction: $(rP imp rP imp rQ) imp rP imp rQ$, <imp.contract>
  / Implication of truths: $rP imp rQ imp rP$, <imp.right-const>
  / Swap: $(rP imp rQ imp rR) imp rQ imp rP imp rR$. <imp.swap>
]
#proof[
  + We need to derive $holds rP$ from $holds rP$. But that is trivial.
  + We need to derive $holds (rP imp rQ) imp rP imp rR$ from 
    $holds rQ imp rR$, e.g. derive $holds rP imp rR$ from 
    $holds rQ imp rR$ and $holds rP imp rQ$,
    so it suffices to derive $holds rR$ from $das(1,holds rQ imp rR
    )$, $das(2,holds rP imp rQ)$, and $das(3,holds rP)$. 

    From #n[modus ponens]#justifytas(3,2), we get $das(4,holds rQ)$ from $holds rP$, $holds rP imp rQ$. Again using #n[modus ponens]#justifytas(1,4) on $holds rQ$ and $holds rQ imp rR$, $holds rR$ follows.
  + Similarly to above, assume #das(1)[$holds rP imp rP imp rQ$] and #das(2)[$holds rP$].
    Then, #n[modus ponens]#justifytas(1,2) shows #das(3,$holds rP imp rQ$), and, again using #n[modus ponens]#justifytas(2,3), one has $holds rQ$.
  + Assume $das(1,holds rP), das(2,holds rQ)$. We need to show $holds rP$, but that is 
    already #ras(1)[one of our assumptions].
  + Assume $das(1,holds rP imp rQ imp rR), das(2,holds rQ), das(3,holds rP)$. By #n[modus ponens]#justifytas(1,3), $das(4,holds rQ imp rR)$, by #n[modus ponens]#justifytas(2,4), $holds rR$.]

#remark(title: "Omitting the tack")[
  If no confusion arises between asserting the truth of a #n[proposition] $dv(P)$ and just naming it, we often write just $rP$ instead of $holds rP$.
]

==== Conjunction
#definition(title: "Conjunction")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<and>)[conjunction] $rP and rQ$ to be #n[true], both $rP$ and $rQ$ must #n[hold]. Also, from $holds rP and rQ$, one can derive $holds rP$, $holds rQ$.
]
#names(<and>, "logic.and", "logic.as well as", "conjunction", "logic.both", "conjunctions")

#let conj = $#lk(<and>, math.and)$

#proposition(title: "Implication and conjunction")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following always #n[hold]:
  / #n[Conjunction] introduction: $rP imp rQ imp rP conj rQ$, <and.intro>
  / #n[Conjunction] elimination: $rP conj rQ imp rP$, $rP conj rQ imp rQ$, <and.elim>
  / #n[Conjunction] mapping: $(rP imp rQ) imp (rR imp rS) imp (rP conj rR) imp (rQ conj rS)$. <and.map>
]
#proof[
  + Assume $rP, rQ$. Then, by #lk(<and>)[definition], $rP conj rQ$ must hold.
  + Assume $rP conj rQ$. Then we can derive $rP$ and $rQ$ respectively, also by #link(<and>)[definition].
  + Assume $rP imp rQ, rR imp rS, rP conj rR$. Then, by #lk(<and.elim>, [elimination]), we have $rP, rR$. From #n[modus ponens] it follows that $rQ$ as well as $rS$, hence by #lk(<and.intro>,[introduction]), $rQ conj rS$.
  ]
==== Logical equivalence
#definition(title: "Logical equivalence")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, the #n[proposition] given by the #def(<iff>)[equivalence] $rP arrow.l.r.double rQ$ between $rP$, $rQ$ is defined as $(rP imp rQ) conj (rQ imp rP)$. It is often read as "$rP$ iff $rQ$".
]
#names(<iff>, "iff", "if and only if", "equivalently", "biconditional", "biconditionals", "logic.equivalent")
#let iff = $#lk(<iff>, math.arrow.l.r.double)$

#remark(title: "Equivalence conventions")[
  We usually prove #lk(<iff>,[equivalence statements]) by showing both directions. E.g. to prove $dv(P) iff dv(Q)$, we first assume $rP$ and show $rQ$ (the "only if" direction), then assume $rQ$ and show $rP$ (the "if" direction).

  We will also see that if $rP iff rQ$ #n[holds], we can always replace $rP$ by $rQ$ in a #n[statement] without changing whether it is a #n[tautology], which we will often implicitly utilize.

  More fundamentally, if $rP iff rQ$ and $rP$ #n[hold], so must $rQ$, and if $rP iff rQ$ and $rQ$ #n[hold], so must $rP$.
]

#proposition(title: "Logical equivalence is like an equivalence relation")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following must #n[hold]:
  / Reflexivity: $rP iff rP$, <iff.refl>
  / Symmetry: $(rP iff rQ) imp (rQ iff rP)$, <iff.symm>
  / Transitivity: $(rQ iff rR) imp (rP iff rQ) imp (rP iff rR)$, <iff.trans>
]<iff.equiv>
#proof[
  + We must show that $(rP imp rP) and (rP imp rP)$, so it
    suffices#justifyt(<and.intro>) to show $rP imp rP$, $rP imp rP$, 
    both of which are known#justifyt(<imp.refl>).
  + Assume $rP imp rQ, rQ imp rP$. To show $rQ iff rP$, we need   
    to#justifyt(<iff>) deduce $rQ imp rP, rP imp rQ$, which is just our 
    assumptions in reverse order.
  + Assume $rQ imp rR, rR imp rQ, rP imp rQ, rQ imp rP$. We need to show 
    $rP imp rR, rR imp rP$.
    + Assume $rP$. By #n[modus ponens], we have $rQ$, again by
      #n[modus ponens], we have $rR$.
    + Assume $rR$. By #n[modus ponens], we have $rQ$, again by
      #n[modus ponens], we have $rP$.
]

#proposition(title: "Operations respect equivalence")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions] such that $rP iff rQ$ #nn[and][logic] $rR iff rS$. Then, the following must #n[hold]:
  / Equivalence respects equivalence: $(rP iff rR) iff (rQ iff rS)$, <iff.congr>
  / Implication respects equivalence: $(rP imp rR) iff (rQ imp rS)$, <imp.congr>
  / Conjunction respects equivalence: $(rP conj rR) iff (rQ conj rS)$. <and.congr>
]
#proof[
  + One must show $(rP iff rR) imp (rQ iff rS)$, $(rQ iff rS) imp (rP iff rR)$.
    + Assume $rP iff rR$. Then#justifyt(<iff.symm>), $rR iff rP$, such that#justifyt(<iff.trans>) $rR iff rQ$, and#justifyt(<iff.symm>) $rQ iff rR$, such that finally, by #lk(<iff.trans>)[transitivity] and $rR iff rS$, we have $rQ iff rS$.
    + Assume $rQ iff rS$. #lk(<iff.trans>)[Transitivity] with $rP iff rQ$ shows $rP iff rS$. We also have#justifyt(<iff.symm>) $rS iff rR$, such that once again by #lk(<iff.trans>)[transitivity], $rP iff rR$ follows.
  + We show both directions.
    + Assume $rP imp rR$ and $rQ$. From $rP iff rQ$, we can see that $rP$ #n[holds], by #n[modus ponens], so does $rR$, from $rR iff rS$ we can see that $rS$ #n[holds], too. Hence $rQ imp rS$.
    + Assume $rQ imp rS$ and $rP$. From $rP iff rQ$, we can see that $rQ$ #n[holds], by #n[modus ponens], so does $rS$, from $rR iff rS$ we can see that $rR$ #n[holds], too. Hence $rP imp rR$.
  + We show both directions.
    + Assume $rP conj rR$. Then $rP$, $rR$ both #n[hold]#justifyt(<and.elim>). Hence by assumption, so does $rQ$ and $rS$ respectively. Thus#justifyt(<and.intro>) $rQ conj rS$ does too.
    + Assume $rQ conj rS$. Then $rQ$, $rS$ both #n[hold]#justifyt(<and.elim>). Hence by assumption, so does $rP$ and $rR$ respectively. Thus#justifyt(<and.intro>) $rP conj rR$ does too.   
]
#proposition(title: [Properties of conjunction])[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, the following #n[hold]:
  / Currying: $((rP conj rQ) imp rR)) iff (rP imp rQ imp rR)$. <and.curry>
  / Implying conjunctions: $(rP imp (rQ conj rR)) iff ((rP imp rQ) and (rP imp rR))$, <and.imp-into>
  / Idempotence: $(rP conj rP) iff rP$, <and.self>
  / Commutativity: $(rP conj rQ) iff (rQ conj rP)$, <and.comm>
  / Associativity: $(rP conj (rQ conj rR)) iff ((rP conj rQ) conj rR)$. <and.assoc>
]
#proof[
  + We show both sides.
    + Assume $((rP conj rQ) imp rR), rP, rQ$. Then#justifyt(<and.intro>), we have $rP conj rQ$, hence by #n[modus ponens], $rR$ follows. This shows $rP imp rQ imp rR$.
    + Assume $rP imp rQ imp rR, rP conj rQ$. Then by #lk(<and.elim>)[elimination], $rP$ as well as $rQ$ must be true. Hence by double #n[modus ponens], $rR$ follows. So $(rP conj rQ) imp rR$ must hold.
  + We show both sides.
    + Assume $rP imp (rQ conj rR)$. We need#justifyt(<and.intro>) to show $rP imp rQ$ as well as $rP imp rR$.
      + Assume $rP$. Then by #n[modus ponens], $rQ conj rR$ holds. Thus by #lk(<and.elim>)[elimination], so does $rQ$.
      + Assume $rP$. Then by #n[modus ponens], $rQ conj rR$ holds. Thus by #lk(<and.elim>)[elimination], so does $rR$.
    + Assume $rP imp rQ, rP imp rR, rP$. By #n[modus ponens], we have $rQ, rR$, hence#justifyt(<and.intro>) $rQ conj rR$. This shows $rP imp (rQ conj rR)$.
  + We show both sides. Assume $rP conj rP$, by #lk(<and.elim>)[elimination], $rP$ immediately follows. Now assume $rP$. By #lk(<and.intro>)[introduction], we have $rP imp rP imp rP conj rP$, #lk(<imp.contract>)[contraction] implies $rP imp rP conj rP$ as desired.
  + We show the left-to-right-implication, the other follows from renaming the variables. Assume $rP conj rQ$. Then $rP, rQ$ must hold. Hence $rQ, rP$ hold and by #lk(<and.intro>)[introduction], so does $rQ conj rP$.
  + We show both sides.
    + Assume $rP conj (rQ conj rR)$. By #lk(<and.elim>)[elimination], we have $rP, rQ conj rR$ and finally $rP, rQ, rR$. We use #lk(<and.intro>)[introduction] to show $rP conj rQ$ and use it again to show $(rP conj rQ) conj rR$.
    + Assume $(rP conj rQ) conj rR$. By #lk(<and.elim>)[elimination], we have $rP conj rQ, rR$ and finally $rP, rQ, rR$. We use #lk(<and.intro>)[introduction] to show $rQ conj rR$ and use it again to show $rP conj (rQ conj rR)$.
]
#remark(title: [Associativity of conjunction])[
  By a metamathematical argument, we can see that whatever way we insert brackets in a #n[conjunction] $dv(P)_1 conj dv(P_2) conj dots conj dv(P_n)$, by #lk(<and.assoc>)[associativity], all of them turn out to be equivalent. Hence we omit any discussion of this issue and tacitly assume $conj$ to associate to the, say, left. We will almost never use brackets and instead directly deduce $rP_1, dots, rP_n$ directly from $rP_1 and dots and rP_n$ etc.
]<and.assoc-notation>
==== Disjunction
#let disj = $#lk(<or>, math.or)$
#definition(title: "Conjunction")[
  Let $dv(P), dv(Q), dv(R)$ be #n[propositions]. Then, for the #n[proposition] given by the #def(<or>)[disjunction] $rP or rQ$ to be #n[true], there are the introduction rules where from $holds rP$ follows $holds rP disj rQ$ and from $holds rQ$ follows $holds rP disj rQ$, as well as the elimination rule where from $holds rP imp rR, holds rQ imp rR$ and $holds rP disj rQ$ one can conclude $rR$.
]
#names(<or>, "or", "disjunction")
#proposition(title: "Implication and disjunction")[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following always #n[hold]:
  / #n[Disjunction] introduction: $rP imp rP conj rQ, rQ imp rP conj rQ$, <or.intro>
  / #n[Disjunction] elimination: $(rP imp rR) imp (rQ imp rR) imp (rP disj rQ) imp rR$, <or.elim>
  / #n[Disjunction] mapping: $(rP imp rQ) imp (rR imp rS) imp (rP disj rR) imp (rQ disj rS)$. <or.map>
]
#proof[
  + Follows directly from the introduction rules for #n[disjunction].
  + Follows directly from the elimination rules for #n[disjunction].
  + Assume $rP imp rQ, rR imp rS, rP disj rR$. We show $rP imp rQ disj rS, rR imp rQ disj rS$.
    + Furthermore assume $rP$. Then, by #[modus ponens], $rQ$ holds, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$, as needed.
    + Furthermore assume $rR$. Then, by #[modus ponens], $rS$ holds, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$, as needed.
    Hence we can use #lk(<or.elim>)[elimination] to conclude $(rP disj rR) imp (rQ disj rS)$.
  ]

#proposition(title: [Properties of disjunction])[
  Let $dv(P), dv(Q), dv(R), dv(S)$ be #n[propositions]. Then, the following #n[hold]:
  / Disjunction respects equivalence: $rP iff rQ, rR iff rS$ #n[imply] that $(rP disj rR) iff (rQ disj rS)$ <or.congr>
  / Idempotence: $(rP disj rP) iff rP$, <or.self>
  / Commutativity: $(rP disj rQ) iff (rQ disj rP)$, <or.comm>
  / Associativity: $(rP disj (rQ disj rR)) iff ((rP disj rQ) disj rR)$,<or.assoc>
  / Conjunction Distributivity: $rP disj (rQ conj rR) iff ((rP disj rQ) conj (rP disj rR))$ <or.and-distr> and $rP conj (rQ disj rR) iff ((rP conj rQ) disj (rP conj rR))$, <and.or-distr>
  / Absorption Laws: $(rP disj (rP conj rQ)) iff rP$ <or.and-absorb>, $(rP conj (rP disj rQ)) iff rP$, <and.or-absorb>
  / Disjunction, implication and conjunction: $((rP disj rQ) imp rR) iff ((rP imp rR) and (rQ imp rR))$.
  ]
#proof[
  + We show both directions.
    + Apply #lk(<or.elim>)[elimination] to $rP disj rR$.
      + Assume $rP$ holds, then by assumption, so does $rQ$, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$.
      + Assume $rR$ holds, then by assumption, so does $rS$, hence by #lk(<or.intro>)[introduction], so does $rQ disj rS$.
    + Identical argument up to renaming and symmetry.
  + $(rP disj rP) imp rP$ follows from #lk(<or.elim>)[elimination] and #lk(<imp.refl>)[reflexivity of implication], $rP imp rP disj rP$ is just #lk(<or.intro>)[introduction].
  + Assume $rP disj rQ$. Applying #lk(<or.elim>)[elimination], we need to show that $rP imp rQ disj rP$, $rQ imp rQ disj rP$, both of which are instances of #lk(<or.intro>)[introduction]. The other direction is the same up to renaming.
  + We show the left-to-right-case, the other one follows similarly.
    Assume $rP disj (rQ disj rR)$ and apply #lk(<or.elim>)[elimination].
    + We need to show $(rP disj rQ) disj rR$ from $rP$. But this is just two instances of #lk(<or.intro>)[introduction].
    + We need to show $(rP disj rQ) disj rR$ from $rQ disj rR$. Applying #lk(<or.elim>)[elimination] to $rQ disj rR$, it remains to be shown that $rQ imp ((rP disj rQ) disj rR)$ and $rR imp ((rP disj rQ) disj rR)$.
      + Follows from two instances of #lk(<or.intro>)[introduction].
      + Follows from one instance of #lk(<or.intro>)[introduction].
  + We show both laws and both directions.
    + Assume $rP disj (rQ conj rR)$. Apply #lk(<or.elim>)[elimination].
      + Assume $rP$. Then, $rP disj rQ$, $rP disj rR$ hold by left #lk(<or.intro>)[introduction], and so does $(rP disj rQ) conj (rP disj rR)$, by #lk(<and.intro>)[conjunction introduction].
      + Assume $rQ conj rR$. Then, $rP disj rQ$, $rP disj rR$ hold by two right #lk(<or.intro>)[introductions], and so does $(rP disj rQ) conj (rP disj rR)$, by #lk(<and.intro>)[conjunction introduction].
    + Assume $(rP disj rQ) conj (rP disj rR)$, hence we can assume $rP disj rQ$, $rP disj rR$. Apply #lk(<or.elim>)[elimination] on the first.
      + Assume $rP$: Then by #lk(<or.intro>)[introduction], $rP disj (rQ conj rR)$ holds.
      + Assume $rQ$: Do the same on $rP disj rR$ - if $rP$ holds, use #lk(<or.intro>)[introduction] directly, if $rR$ holds, then so does $rQ conj rR$ by #lk(<and.intro>)[introduction], hence by #lk(<or.intro>)[disjunction introduction], we get $rP disj (rQ conj rR)$.
    + Assume $rP conj (rQ disj rR)$, such that we have $rP$ and $rQ disj rR$. Apply #lk(<or.elim>)[elimination] on the #n[disjunction].
      + If we have $rQ$, then $rP conj rQ$ holds, hence $(rP conj rQ) disj (rP conj rR)$ does.
      + If we have $rR$, then $rP conj rR$ holds, hence $(rP conj rQ) disj (rP conj rR)$ does.
    + Assume $(rP conj rQ) disj (rP conj rR)$ holds and use #lk(<or.elim>)[elimination].
      + If $rP conj rQ$ is true, so are $rP, rQ$. Hence $rQ disj rR$ is, and finally $rP conj (rQ disj rR)$.
      + If $rP conj rQ$ is true, so are $rP, rR$. Hence $rQ disj rR$ is, and finally $rP conj (rQ disj rR)$.
  + We show both directions of both laws.
    + Assume $rP disj (rP conj rQ)$ and use #lk(<or.elim>)[elimination].
      If $rP$ is true, we are done, if $rP conj rQ$ is, $rP$ also follows#justifyt(<and.elim>).
    + Assume $rP$, then $rP disj (rP conj rQ)$ immediately#justifyt(<or.intro>) follows.
    + Assume $rP conj (rP disj rQ)$. Then $rP$ follows by #lk(<and.elim>)[elimination].
    + Assume $rP$, then $rP disj rQ$ is true#justifyt(<or.intro>), and so must their #n[conjunction] be#justifyt(<and.intro>), as needed.
  + We show both directions.
    + Assume $(rP disj rQ) imp rR$, we need to show $rP imp rR, rQ imp rR$.
      + Assume $rP$, then $rP disj rQ$ holds, hence by #n[modus ponens], we have $rR$, such that $rP imp rR$.
      + Assume $rQ$, then we have $rP disj rQ$ and proceed similarly.
    + Assume $(rP imp rR) conj (rQ imp rR)$, e.g. $rP imp rR, rQ imp rR$, and $rP disj rQ$. Use #lk(<or.elim>)[elimination] and $rR$ immediately follows.      
]
==== Falsehood and negation
Until now we have only covered a fairly small fragment of propositional logic, e.g. a positive one. By introducing negation, we add substantial complexity and raise some more foundational questions.

#definition(title: "Falsehood")[
  The #def(<false>)[false] #n[proposition] $bot$ is defined such that if $bot$ #n[holds], so does any #n[proposition] $dv(P)$.
]
#names(<false>, "false", "absurd", "contradiction", "contradictions", "falsehood", "absurdity")
#let fls = $#lk(<false>, math.bot)$
#definition(title: "Negation")[
  For any #n[proposition] $dv(P)$, define its #def(<not>)[negation] $not rP$ as $rP imp fls$.
]

#names(<not>, "not", "negation")
#let neg = $#lk(<not>, math.not)$

#definition(title: "Truth")[
  Define the #def(<true>)[true] #n[proposition] $top$ as $neg fls$.
]
#names(<true>, "truth", "triviality")
#let tru = $#lk(<true>, math.top)$

#proposition(title: "True and false")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, the following #n[hold]:
  / Elimination of #n[falsehood]: $fls imp rP$, <false.elim>
  / #n[Falsehood] is false: $neg fls$, <false.false>
  / #n[Truth] is true: $tru$, <true.true>
  / Truth values and #n[biconditionals]: $(tru iff rP) iff rP$, <iff.true> $(fls iff rP) iff neg rP$, <iff.false>
  / Truth values and #n[implications]: $(tru imp rP) iff rP$, $(fls imp rP) iff tru$, $(rP imp tru) iff tru$, $(rP imp fls) iff neg rP$, <imp.true-false>
  / Truth values and #n[conjunction]: $(tru conj rP) iff rP$, $(fls conj rP) iff fls$, <and.true-false>
  / Truth values and #n[disjunction]: $(tru disj rP) iff tru$, $(fls disj rP) iff rP$, <or.true-false>
  / Truth values and #n[negation]: $neg tru iff fls, neg fls iff tru$, <not.true-false>
  / Absurdity: $neg (rP conj neg rP)$, <and.absurd>  
  / Converse implications: $(rP imp rQ) imp neg rQ imp neg rP$, <imp.converse1>
  / #n[Negation] respects equivalence: $(rP iff rQ) imp (neg rP iff neg rQ)$, <not.congr>
  / Double #n[negation]: $rP imp neg neg rP$. <not.not-of>
]
#proof[
  + By definition of $fls$.
  + $neg fls iff (fls imp fls)$, which holds by #lk(<imp.refl>)[reflexivity].
  + Follows from $tru iff neg fls$.
  + If $tru iff rP$, then, since $tru$ is#justifyt(<true.true>) #n[true], so is $rP$. If $rP$ holds, then it also follows from $tru$ such that $rP imp tru$ and the other direction holds anyways.

    If $fls iff rP$, then in particular $(rP imp fls) iff neg P$. If $neg P$ holds, we have $rP imp fls$, and $fls imp rP$ holds anyways#justifyt(<false.elim>), so the #n[biconditional] is established.
  + We show all #n[biconditionals].
    + We have $rP #justify(<iff.true>, iff) (tru iff rP) #justify(<iff>, iff) ((tru imp rP) conj (rP imp tru))$, but the second #n[proposition] is #n[true],#justifyt(<imp.right-const>) as $tru$ is#justifyt(<true.true>), such that the #n[conjunction] is #nn[equivalent][logic] to $tru imp rP$ as desired.
    + By the #lk(<iff.true>)[above]#justifyt(<iff.trans>), we need to show $fls imp rP$ always holds. But that is already #lk(<false.elim>)[known].
    + It suffices#justifyt(<iff.true>) to show $rP imp tru$. But that follows#justifyt(<imp.right-const>) from the #lk(<true.true>)[fact] that $tru$ is #n[true].
    + By #lk(<not>)[definition] and #lk(<imp.refl>)[reflexivity] of #n[implication].
  + We show both #n[biconditionals].
    + $tru conj rP imp rP$ is clear. Assume $rP$, then $tru$ #lk(<true.true>)[is] also #n[true], hence so is $tru conj rP$.
    + $bot conj rP imp bot$ is clear, the other direction follows from #lk(<false.elim>)[falsehood elimination].
  + We show both #n[biconditionals].
    + $tru imp (tru disj rP)$ follows from #lk(<or.intro>)[introduction], the other direction from the #lk(<true.true>)[fact] that $tru$ is #n[true].
    + $P imp (fls disj rP)$  follows from #lk(<or.intro>)[introduction], the other direction from #lk(<or.elim>)[elimination] as well as the #lk(<false.elim>)[fact] that $fls imp rP$ and $rP imp rP$#justifyt(<imp.refl>)
  + We show both #n[biconditionals].
    + We have $not tru #justify(<true>,iff) not not fls iff ((fls imp fls) imp fls)$. But $fls imp fls$ holds#justifyt(<imp.refl>), hence by #n[modus ponens] we have $neg tru imp bot$. The other direction is obvious from #lk(<false.elim>)[elimination].
    + By #lk(<true>)[definition].
  + Assume $rP and neg rP$. Then we have $rP, neg rP$, but $neg rP #justify(<not>,iff) (rP imp fls)$, hence by #n[modus ponens], $fls$ holds.
  + Rewrite $neg rP$ to#justifyt(<not>) $rP imp fls$, $neg rQ$ to $rQ imp fls$. Then, this follows from #lk(<imp.trans>)[transitivity of implications].
  + Assume $rP iff rQ$. To show $neg rP imp neg rQ$, apply #lk(<imp.converse1>)[the previous statement] to $rP imp rQ$, and similarly for the other direction.
  + Assume $rP$. We need#justifyt(<not>) to prove $(rP imp fls) imp fls$, so furthermore assume $rP imp fls$, but then we are done by applying #n[modus ponens].
]
=== Excluded middle
#axiom(title: "Law of the excluded middle")[
  Let $dv(P)$ be a #n[proposition]. Then, $rP disj neg rP$ always holds.
]<excluded-middle>
This axiom has rather far reaching consequences in that, unlike the other rules utilized so far, it has no direct computational analogue and serves as an "oracle". Without it, we would be limited to _intutionistic_ propositional logic n so on n so forth.

#names(<excluded-middle>, "excluded middle", "LEM", "law of the excluded middle")

#proposition(title: "Consequences of classical logic")[
  Let $dv(P), dv(Q)$ be #n[propositions]. Then, the following #n[hold]:
  / Double #n[negation] collapse: $rP iff neg neg rP$ <not.not-iff>,
  / Converses: $(rP imp rQ) iff (neg rQ imp neg rP)$ <imp.converse>,
  / Proof by contradiction: $(neg rP imp rP) imp rP$ <not.contradiction>,
  / Discreteness of #n[propositions]: $(rP iff tru) disj (rP iff fls)$ <propositions-discrete>,
  / De-Morgan for #n[disjunction]: $neg(rP disj rQ) iff (neg rP conj neg rQ)$<not.or>,
  / De-Morgan for #n[conjunction]: $neg(rP conj rQ) iff (neg rP disj neg rQ)$<not.and>.  
]
#proof[
  + One direction has #lk(<not.not-of>)[already been shown]. For $neg neg rP imp rP$, use #n[excluded middle] and consider the cases $rP, neg rP$:
    If $rP$ holds, we are done. If $neg P$ holds, then so does $fls$ by #n[modus ponens], hence $P$ does, too#justifyt(<false.elim>).
  + One direction has #lk(<imp.converse1>)[already been shown]. Now assume $neg rQ imp neg rP$. By the #lk(<imp.converse1>)[proven direction], we can see that $neg neg rP imp neg neg rQ$. Rewrite to $rP imp rQ$#justifyt(<not.not-iff>)#justifyt(<imp.congr>).
  + We #n[equivalently]#justifyt(<not.not-iff>)#justifyt(<imp.congr>) show $(neg rP imp rP) imp neg neg rP$. Assume $neg rP imp rP, neg rP$. Then, by #n[modus ponens], $rP$ follows, which is #n[absurd]#justifyt(<and.absurd>).
  + Rewrite to $rP disj neg rP$#justifyt(<iff.true>)#justifyt(<iff.false>) and use #n[excluded middle].
  + For left-to-right assume $neg(rP disj rQ)$. If $rP$ were true, so would $rP disj rQ$ be#justifyt(<or.intro>), hence $neg rP$ and similarly $neg rQ$, such that $neg rP conj neg rQ$#justifyt(<and.intro>).
   
   Now assume $neg rP, neg rQ, rP disj rQ$. If $rP$ holds, we arrive at a #n[contradiction], if $rQ$ holds, we do to. Hence $rP disj rQ$ cannot be #n[true] and we are done.
  + First assume $neg(rP conj rQ)$. Use #n[excluded middle] on $rP$:
    + if $rP$ holds, we show $neg rQ$: from $rQ$ we could derive#justifyt(<and.intro>) $rP conj rQ$, #n[contradiction]. Hence#justifyt(<or.intro>) $neg rP disj neg rQ$.
    + if $neg rP$ holds, $neg rP disj neg rQ$ immediately follows#justifyt(<or.intro>).
]
#remark(title: [Truth tables])[
  The #lk(<propositions-discrete>)[discreteness property] allows us to check validity of #n[statements] (in some variables) very easily (though the method is computationally expensive): just enumerate all the possible cases. For example, we wish to check whether for all #n[propositions] $dv(P), dv(Q)$, $neg rP imp ((rP disj rQ) iff (rP conj rQ))$ is a #n[tautology], so let us consider a table:
  #table(
    columns: 7,
    $dv(P)$, $dv(Q)$, $neg rP$, $rP disj rQ$, $rP conj rQ$, $(rP disj rQ) iff (rP conj rQ)$, $neg rP imp (rP disj rQ) iff (rP conj rQ)$,
    $fls$, $fls$, $tru$, $fls$, $fls$, $tru$, $tru$, 
    $fls$, $tru$, $tru$, $tru$, $fls$, $fls$, $fls$,
    $tru$, $fls$, $fls$, $tru$, $fls$, $tru$, $tru$,
    $tru$, $tru$, $fls$, $tru$, $tru$, $tru$, $tru$
  )
  We can see that this #n[statement] is true unless $rP$ is #n[false] and $rQ$ is #n[true] and in particular, it is not tautological.
]
#remark(title: [Nullary operations])[
  Sometimes, #n[propositions] such as $dv(P)_1 disj dots disj rP_dv(n)$ are considered. If $n = 0$, one defines this as #n[false], and similarly $rP_1 conj dots conj rP_rn$ is #n[true] to not violate #lk(<or.assoc>)[associativity].
]
=== First-Order Logic
The logic previously described clearly does not suffice to do any "serious" mathematics in --- it has no notion of equality, and does not allow for #n[statements] about any _objects_, 
only about other #n[propositions]. Hence, we introduce quantifiers. These require a notion of term variable
that is allowed to appear in the body. For example, if we want to state "All $dv(x)$ possess property $dv(P)(rx)$", 
$rx$ must clearly appear in $rP(rx)$ in some way, but the name of $rx$ itself does not matter,
as "All $dv(y)$ possess property $rP(ry)$" obviously has the same meaning. We will treat these 
basic rules of replacement of terms as given. 

#definition(title: "Terms")[
#def(<term>)[Terms] in general are an undefined sort that in particular include term variables. 
]
#names(<term>, plural:true, "term", "object")
==== Quantifiers
#let forall(x) = $#lk(<all>, math.forall) dv(#x).$
#definition(title: "Universal quantification")[
  Let $dv(P)(dv(x))$ be a #n[proposition] in which (next to other variables) $rx$ might appear.
  Then, the #n[proposition] given by the #def(<all>)[universal quantification] of $rP$ in $rx$ is denoted
  $forall(x) rP(rx)$ (read: "all $dv(x)$ are $rP$/fulfill $rP(rx)$"). It conforms to the following rules:
  + If $rP(rx)$ can be derived from hypotheses in which $rx$ does not appear, $forall(x) rP(rx)$ holds. <all.intro>
  + From $forall(x) rP(rx)$ and any #n[term] $dv(t)$, we can derive $rP(rt)$. <all.elim>
]
#names(<all>, "for all", "all", "every", "Universal quantification", "any", "for any", "Universal quantifier", "universal quantifiers", "universally quantified")
#remark(title: "Proofs of universally quantified statements")[
  Assume $dv(P)(x)$ is some #n[proposition] that declares "type information", e.g. for all $dv(x)$, we have $rP(rx) iff rx "is a group"$. Then, to prove #n[propositions] of the form $forall(x) rP(rx) imp dv(Q)(rx)$ for some other #n[proposition] $rQ(x)$, we usually start proofs like "Let $rx$ fulfill $rP$ (i.e. be a group)" and conclude "Hence, $rx$ fulfills $rQ$".
]
#proposition(title: "Universal quantification and connectives")[
  Let $dv(P)(dv(x)), dv(Q)(rx)$ be #n[propositions], $dv(R)$ a #n[proposition] in which $rx$ does not appear. Furthermore, let $dv(S)(rx,dv(y))$ be a #n[proposition]. Then, we have the following:
  / #n[Universal quantification] of constant #n[propositions]: $rR iff forall(x) rR$, <all.const>
  / #n[Universal quantification] and #n[implication]: $(forall(x) rP(rx) imp rQ(rx)) imp (forall(x) rP(rx)) imp forall(x) rQ(rx)$, <all.imp>
  / #n[Universal quantification] and #n[conjunction]: $(forall(x) rP(rx) conj rQ(rx)) iff (forall(x) rP(rx) conj forall(x) rQ(rx))$, <all.and>
  / #n[Universal quantification] and #n[disjunction]: $(forall(x) rP(rx) disj forall(x) rQ(rx)) imp (forall(x) rP(rx) disj rQ(rx))$, <all.or>
  / #n[Universal quantification] and #n[biconditionals]: $(forall(x) rP(rx) iff rQ(rx)) imp (forall(x) rP(rx)) iff forall(x) rQ(rx)$, <all.iff>
  / #n[Universal quantification] and #n[disjunction] (special case): $(forall(x) rP(rx) disj rR) iff ((forall(x) rP(rx)) disj rR)$, <all.or-const>
  / Swapping #n[universal quantifiers]: $(forall(x) forall(y) rS(rx,ry)) iff (forall(y) forall(x) rS(rx,ry))$. <all.swap>
]
#proof[
  + $rR imp forall(x) rR$ follows from the #lk(<all.intro>)[introduction rule], as $rx$ does not appear in the hypothesis $rR$. The other direction follows from #lk(<all.elim>)[elimination].
  + Assume $forall(x) rP(rx) imp rQ(rx), forall(x) rP(rx)$ and use #lk(<all.intro>)[introduction] to obtain an $dv(y)$ for which we have to prove $rQ(ry)$.
    Then, by #lk(<all.elim>)[elimination], we have $rP(ry) imp rQ(ry)$ and $rP(ry)$, hence $rQ(ry)$ as needed.
  + We prove both directions:
    + Assume $forall(x) rP(rx) conj rQ(rx)$. We need to show $forall(y) rP(ry)$,
      $forall(z) rQ(rz)$ respectively. #lk(<all.intro>)[Introduce] $dv(y)$. Then by #lk(<all.elim>)[elimination], we have $rP(ry) conj rQ(ry)$, hence in particular#justifyt(<and.elim>) $rP(ry)$ as needed. The same argument works for $forall(z) rQ(rz)$.
    + Assume $forall(x) rP(rx), forall(x) rQ(rx)$#justifyt(<and.elim>) and #lk(<all.intro>)[introduce] $dv(y)$. Then, by assumption#justifyt(<all.elim>), we have $rP(ry), rQ(ry)$, hence#justifyt(<and.intro>) $rP(ry) conj rQ(ry)$, such that $forall(y) rP(ry) conj rQ(ry)$. 
  + First#justifyt(<or.elim>), assume $forall(x) rP(rx)$ and #lk(<all.intro>)[introduce] $dv(y)$. Then clearly, $rP(ry)$#justifyt(<all.elim>) and $rP(ry) disj rQ(ry)$#justifyt(<or.intro>), hence $forall(y) rP(ry) disj rQ(ry)$. Similar reasoning works if $forall(x) rQ(rx)$ #n[holds].
  + From the definition of #n[iff], we have $ (forall(x) rP(rx) iff rQ(rx)) #justify(<all.and>, iff) (forall(x) rP(rx) imp rQ(rx) conj forall(x) rQ(rx) imp rP(rx)). $
    Hence#justifyt(<all.imp>) $forall(x) rP(rx) imp forall(x) rQ(rx)$, $forall(x) rQ(rx) imp forall(x) rP(rx)$ and we are done#justifyt(<iff>)#justifyt(<and.intro>).
  + One direction follows from #lk(<all.or>)[above]. For the other, use #n[excluded middle] on $rR$: If $rR$ #n[holds], we are done#justifyt(<or.intro>), if $neg rR$ does, we will show $forall(x) rP(rx)$. #lk(<all.intro>)[Introduce] $dv(x)$. Then#justifyt(<all.elim>) by assumption, $rP(rx) disj rR$. But the latter would be #lk(<and.absurd>)[contradictory], hence $rP(rx)$ and we are done.
  + Assume $forall(x) forall(y) rS(x,y)$ and introduce#justifyt(<all.intro>) $dv(w),dv(v)$. Then, by assumption#justifyt(<all.elim>), $forall(y) rS(rv(v),ry)$ hence also $rS(rv(v), rw)$ which is precisely what we needed to show.
]
#let exists(x) = $#lk(<exists>, math.exists) dv(#x).$
#definition(title: "Existential quantification")[
  Let $dv(P)(dv(x))$ be a #n[proposition] in which (next to other variables) $rx$ might appear and $dv(Q)$ a #n[proposition] in which $rx$ does not appear.
  Then, the #n[proposition] given by the #def(<exists>)[existential quantification] of $rP$ in $rx$ is denoted
  $exists(x) rP(rx)$ (read: "there exists a $dv(x)$ that is $rP$"). It conforms to the following rules:
  + For any #n[term] $dv(t)$ and $rP(rt)$, we can derive $exists(x) rP(rx)$. <exists.intro>
  + If we can derive $rQ$ from $rP(rx)$ such that $rx$ appears in no other hypothesis and $exists(x) rP(rx)$ holds, then so does $rQ$. <exists.elim>
]
#remark(title: [Existential quantification in proofs])[
  To apply #lk(<exists.elim>)[existential elimination] on $exists(x) dv(P)(rx)$, we often word proofs like "We obtain an $dv(x)$ such that $rP(rx)$" or similar. To apply #lk(<exists.intro>)[existential introduction], a common phrasing is "Use $x$, we show that it satisfies $rP$".
]
#names(<exists>, "for any", "for some", "exist", "exists", "Existential quantification", "Existential quantifier", "existential quantifiers", "existence")
#proposition(title: "Existential quantification and connectives")[
  Let $dv(P)(dv(x)), dv(Q)(rx)$ be #n[propositions], $dv(R)$ a #n[proposition] in which $rx$ does not appear. Furthermore, let $dv(S)(rx,dv(y))$ be a #n[proposition]. Then, we have the following:
  / #n[Existential quantification] of constant #n[propositions]: $rR iff exists(x) rR$, <exists.const>
  / #n[Existential quantification] and #n[implication]: $((exists(x) rP(rx)) imp exists(x) rQ(rx))) imp (exists(x) rP(rx) imp rQ(rx))$, <exists.imp>
  / #n[Existential quantification] and #n[implication] in a #n[universal quantifier]: $(exists(x) rP(rx)) imp (forall(x) rP(rx) imp rQ(rx)) imp (exists(x) rQ(rx))$, <exists.all-imp>
  / #n[Existential quantification] and #n[conjunction]: $(exists(x) rP(rx) conj rQ(rx)) imp (exists(x) rP(rx) conj exists(x) rQ(rx))$, <exists.and>
  / #n[Existential quantification] and #n[disjunction]: $(exists(x) rP(rx) disj exists(x) rQ(rx)) iff (exists(x) rP(rx) disj rQ(rx))$, <exists.or>
  / #n[Existential quantification] and #n[conjunction] (special case): $(exists(x) rP(rx) conj rR) iff ((exists(x) rP(rx)) conj rR)$, <exists.and-const>
  / #n[Existential quantification] and #n[biconditionals] in a #n[universal quantifier]: $(forall(x) rP(rx) iff rQ(rx)) imp (exists(x) rP(rx)) iff (exists(x) rQ(rx))$, <exists.all-iff>,
  / Swapping #n[existential quantifiers]: $(exists(x) exists(y) rS(rx,ry)) iff (exists(y) exists(x) rS(rx,ry))$ <exists.swap>,
  / #n[Existential quantifiers], #n[universal quantifiers] and #n[negation]: $(exists(x) neg rP(rx)) iff neg (forall(x) rP(rx))$ and $(forall(x) neg rP(rx)) iff neg (exists(x) rP(rx))$ <exists.not-all>,
  / #n[Existential quantifiers] and #n[universal quantifiers] "swapping": $(exists(x) forall(y) rS(rx,ry)) imp forall(y) exists(x) rS(rx,ry)$ <exists.exists-all-all-exists>.
]
#proof[
  + One direction is just the #lk(<exists.intro>)[introduction rule]. The other one follows from #lk(<exists.elim>)[elimination] because we can derive $rR$ from $rR$ no matter what.
  + Assume $((exists(x) rP(rx)) imp exists(x) rQ(rx)))$ and use #n[excluded middle] on $exists(x)(rP(rx))$. If it holds, so does $exists(x) rQ(rx)$. Now use#justifyt(<exists.intro>) the $dv(x)$ fulfilling $rQ(rx)$ - clearly, it also fulfills $rP(rx) imp rQ(rx)$. If $neg exists(x)(rP(rx))$ holds, also use that $rx$. Since it fulfills $neg rP(rx)$, $rP(rx) imp rQ(rx)$ is true by #lk(<and.absurd>)[contradiction].
  + Assume $exists(x) rP(rx)$ and $forall(x) rP(rx) imp rQ(rx)$. Obtain some $dv(x)$ with $rP(rx)$. Then, we must also have $rQ(rx)$. Use that $rx$, and we have shown $exists(x) rQ(rx)$.
  + Assume $exists(x) rP(rx) conj rQ(rx)$ and obtain a $dv(x)$ such that $rP(rx)$, $rQ(rx)$. Then, use that $rx$ to show $exists(x) rP(rx)$, $exists(x) rQ(rx)$.
  + We show both directions.
    + If $exists(x) rP(rx)$, we can see#justifyt(<exists.all-imp>)#justifyt(<or.intro>) that $exists(x) rP(rx) or rQ(rx)$. Similarly for $exists(x) rQ(rx)$.
    + Obtain an $dv(x)$ with $rP(rx) disj rQ(rx)$. If $rP(rx)$ holds, use that $rx$ to show $exists(x) rP(rx)$, hence $exists(x) rP(rx) disj exists(x) rQ(rx)$. If $rQ(rx)$ holds, use similar reasoning.
  + The left-to-right direction follows from above#justifyt(<exists.and>). So assume $(exists(x) rP(rx) conj rR)$, e.g. obtain an $dv(x)$ with $rP(rx)$ while $rR$ also holds. Then, $rP(rx) conj rR$ also holds, hence by #lk(<exists.intro>)[introduction], we get $exists(x) rP(rx) conj rR$.
  + Assume $forall(x) rP(rx) iff rQ(rx)$. Then in particular#justifyt(<iff>)#justifyt(<all.imp>), $forall(x) rP(rx) imp rQ(rx)$, hence#justifyt(<exists.all-imp>) $exists(x) rP(rx) imp exists(x) rQ(rx)$. Similar for the other direction.
  + Assume $exists(x) exists(y) rS(rx,ry)$. Now obtain an $dv(x)$ such that $exists(y) rS(rx, ry)$ and do it again to obtain a $dv(y)$ with $rS(rx,ry)$. 
    Now $exists(v)rS(rv(v),ry)$ follows by using $rx$ and $exists(w)exists(v)rS(rv(v),rw)$ follows by using $ry$.
  + We show both statements:
    + We show both directions:
      + Assume $exists(x) neg rP(rx)$ and $forall(x) rP(rx)$. Obtain an $dv(x)$ with $neg rP(rx)$. Then, by assumption, $rP(rx)$. #n[Contradiction]. Note that this direction does not require #n[excluded middle].
      + Assume $neg forall(x) rP(rx)$. It suffices to show $neg neg exists(x) neg rP(rx)$ by #lk(<not.not-iff>)[double negation elimination]. So by taking the #lk(<imp.converse>)[converse] we need to show $(neg exists(x) neg rP(rx)) imp forall(x) rP(rx)$. So assume $neg exists(x) neg rP(rx)$ and introduce some $dv(x)$. We need to show $rP(rx) #justify(<not.not-iff>,iff) neg neg rP(rx)$. So assume $neg rP(rx)$ -- then, use $rx$ to show $exists(x) neg rP(rx)$, #n[contradiction].
    + From the first statement applied to $neg rP(rx)$, we obtain 
      $(exists(x) neg neg rP(rx)) iff neg (forall(x) neg rP(rx))$.
      So $ neg (exists(x) rP(rx)) #justify(<exists.all-iff>, iff) neg (exists(x) neg neg rP(rx)) #justify(<not.congr>,iff) neg neg (forall(x) neg rP(rx)) #justify(<not.not-iff>, iff) forall(x) neg rP(rx). $
  + Obtain an $dv(x)$ such that $forall(y) rS(rx, ry)$ and introduce $dv(y)$. Then $rS(rx, ry)$, such that if we use $rx$, we are done.
  ]

==== Equality
So far, no way of actually incorporating terms in formulas has been constructed, such that no expressive power is gained. This now changes.

#definition(title: [Equality])[
  Let $dv(t), dv(s)$ be #n[terms]. Then, the #n[proposition] $t = s$ asserts their #def(<eq>)[equality].
  It conforms to the following rules:
  / Reflexivity: for all #n[terms] $dv(t)$, $rt = rt$ #n[holds], <eq.refl>
  / Substitution: for all #n[terms] $dv(t), dv(s)$ with $rt = rs$ and any #n[proposition] $dv(P)(rt)$ that #n[holds] and in which $rt$ appears, any instance of $rt$ can be replaced by $rs$ and it still #n[holds]. <eq.subst>
]
#show "=": it => link(<eq>,$=$)
#let neq = link(<eq>,$eq.not$)
#names(<eq>, "equals", "same", "identical", "identity", "equal",
      "identities", "equalities", "equation")

#proposition(title: [Elementary properties of equality])[
  Let $dv(t), dv(s), dv(r)$ be #n[terms], $dv(u)(rt)$ be a #n[term] in which $rt$ appears, $dv(P)(rt)$ a #n[proposition] in which $rt$ appears. Then, the following #n[hold]:
  / Symmetry: $rt = rs imp rs = rt$<eq.symm>,
  / Transitivity: $rs = rr imp rt = rs imp rt = rr$<eq.trans>,
  / Substitution (reworded): $rt = rs imp (rP(rt) iff rP(rs))$,
  / Term substitution: $ru(rt) = ru(rs)$, where $ru(rs)$ denotes the substitution of $rt$ by $rs$.<eq.congr>
  In particular, all of these hold when $rt, rs$ are variables and #n[universally quantified].
]
#let defiff = link(<handle-definitions>, $:arrow.l.r.double$)
#let defeq = link(<handle-definitions>, $:=$)
#proof[
  + Assume $rt = rs$. Then apply #lk(<eq.subst>)[substitution] to the assumption and $dv(Q)(dv(x)) defiff rx = rt$. The instance $rQ(rt)$ clearly holds from #lk(<eq.refl>)[reflexivity] such that we can conclude $rs = rt$.
  + Assume $rs = rr, rt = rs$. Apply #lk(<eq.subst>)[substitution] to $dv(Q)(dv(x)) defiff rt = rx$. Then one assumption gives us $rQ(rs)$ and from $rs = rr$ we can conclude $rQ(rr) defiff rt = rr$ as desired.
  + Assume $rt = rs$ and $rP(rr)$, then $rP(rs)$ follows from #lk(<eq.subst>)[substitution]. The other direction follows from #lk(<eq.subst>)[substitution] and #lk(<eq.symm>)[symmetry].
]
#remark(title: "How to handle definitions")[
  In mathematics, one often defines #n[terms] and properties, usually based on existing ones. How do we handle this in our logic? There are multiple options.
  - Consider definitions purely metamathematically and treat a definition like $f(x) := 2x$ just as a shorthand to the reader. This is among the simpler options, but comes with issues. When we define a function $f$ as above, we want to be able to treat it as an object on its own. But if $f(x) := 2x$ is just a replacement rule, $f$ on its own makes no sense mathematically. This can be taken care of by introducing extra syntax where $f(x) := 2x$ is, on its own, a shorthand for $f := x mapsto 2x$, which is mathematically coherent.
  - Add definitions as axioms, whose conservativity can be proven: For every #n[term] $t$ we define, we add a new primitive symbol $t$ and assert that $t$ is equal to its definition like we assert say reflexivity. We can then metamathematically prove that these definitional axioms do not fundamentally alter our system, i.e. do not allow us to prove anything new the symbol does not appear in. However, it seems philosophically unsatisfactory. For an example, see @metamath.
  - Integrate definitions in our logic: We could add new types of sentences that reflect definitions more directly, as is done in programming languages, and while this is the most powerful option, it is unwieldy and it is easy to accidentially arrive at inconsistent systems.
  We will mostly stick to option 1. Whenever a new "type" of definition appears, like for relations or functions, we will quickly take note of it. However, one more problem arises: many mathematical definitions take the form of "define $dv(t)$ as the unique $dv(x)$ such that $dv(P)(rx)$". This does not translate to any term on its own --- in notation, we know something along the lines of $exists(x) rP(rx) conj forall(y) rP(ry) imp ry = rx$ (which we will soon use as the definition of unique existence), but we cannot name that $rx$ in any term. A simple solution: Prepend every #n[proposition] $dv(Q)$ considered after to turn it into $forall(t) rP(rt) imp rQ$. Now every occurrence of $rt$ is known to satisfy its property and it can be proven to be unique in it from context.

  There are also more logical approaches that allow you to directly name the object $rt$ with _description operators_ - denote such an operator by $iota$, then $iota_(rx)(rP)$ would refer to the #n[term] $t$ and be well-defined due to the unique existence. However, such operators can have surprisingly far-reaching logical consequences (for example, imply the axiom of choice as in @bourbaki-sets).

  From now on, we will use $defiff$ and $defeq$ for definitions of #n[propositions] and #n[terms] respectively. If we are given $dv(P) defiff dv(Q)$, $dv(t) defeq dv(s)$, then $rP iff rQ$ and $rt = rs$ hold by #lk(<eq.refl>)[reflexivity]#justifyt(<iff.refl>).
]<handle-definitions>

#let exists1(x) = $#lk(<exists1>, $#sym.exists !$) dv(#x).$

#definition(title: [Unique existence])[
    Let $dv(P)(dv(x))$ be a #n[proposition] in which (next to other variables) $rx$ might appear. Then we set
    $ exists1(x) rP(rx) defiff exists(x) rP(rx) conj (forall(y) rP(ry) imp ry = rx). $
]<exists1>
#proposition(title: [Unique existence of equality])[
  For every #n[term] $dv(t)$ we have $exists1(x) rt = rx$.
]
#proof[
  Use $dv(t)$, then clearly, $rt=rt$#justifyt(<eq.refl>). It remains to show#justifyt(<exists1>) that #n[for all] $dv(y)$ with $rt = ry$, we have $ry = rt$. But that follows from #lk(<eq.symm>)[symmetry].
]