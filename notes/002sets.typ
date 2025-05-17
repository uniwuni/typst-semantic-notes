#import "001logic.typ": *
== Basic set theory
This part is largely oriented around the first few chapters of @axiomatic-set-theory due to its detailed and rigorous treatment of the very basics of set theory as a foundation.

Over the last few sections, we have developed the first steps of a theory of #n[terms], but without any interpretation attached, leaving it unclear what they should represent. This is mostly an advantage that leaves the developed first-order logic very general and makes it able to contain topics as distinct as abelian groups and dense linear orders. 

However, from now on we will consider #n[terms] as standing for _sets_ --- what these are remains undefined, but every single concept we concern ourselves with can be reduced to a construct of sets. Of course, there are other foundations, some of which, like many type theories, more closely match the informal foundations used in everyday mathematics.
But they are substantially harder to develop formally and there is still too much disagreement about which of the dozens of slightly different theories should be preferred, disagreement that has mostly been settled for set theory (unless, of course, you start talking to set theorists).

Hence from now on, the following "definition" applies:
#definition(title: "Sets")[
  A #def(<set>)[set] is anything quantified over, i.e. the preferred interpretation of the elements of the universe the variables range over.
]
#names(<set>,"set","sets")
#n[Sets] are defined by their elements, hence we need a notion of elements. In informal mathematics one usually considers #n[sets] of numbers, group elements, fruit (mostly occurring on primary school level) and so forth.
While we will be able to deal with most of these by defining them into #n[existence] (excluding the fruit), currently the only thing a #n[set] can contain is other #n[sets]. Hence we declare:
#definition(title: "Membership")[
  If $dv(t), dv(s)$ are two #n[terms], then $rt in rs$ (read: $rt$ is an element of $rs$) is a #n[proposition] that expresses #def(<mem>)[membership] of $rt$ in $rs$.
]
#let mem = $#lk(<mem>, math.in)$
#let nmem = $#lk(<mem>, math.in.not)$
#names(<mem>, "element","member",plural:true)
#names(<mem>, "in")

Admittedly this is less of a definition than it is a declaration or an axiom, since $dv(t) mem dv(s)$ is not assigned any definiens.

We take an _extensional_ point of view in which #n[sets] are fully defined by their #n[elements] as opposed to some other structure that only changes how we arrive at their elements. These _intensional_ equalities often make sense in more computational theories as they can incorporate algorithmic complexity or termination behavior.

#axiom(title: "Extensionality")[
  #n[For all] #n[sets] $dv(x),dv(y)$,
  $ (forall(z) rz mem rx iff rz mem ry) imp rx=ry. $
]<set.ext>
#names(<set.ext>, "extensionality")

We will often end up with collections that are too large to be a #n[set], e.g. the collection of all groups. This requires us to deal with _classes_.

#definition(title: "Class")[
  A #def(<class>)[class] is a definable property of #n[sets], e.g. a #n[proposition] $dv(P)(dv(x), dv(a_1), ..., dv(a_n))$. We write $dv(x) in rP$ #n[iff] $rP(rx)$. Two classes $dv(P), dv(Q)$ are considered equal if $forall(x)rP(rx) iff rQ(rx)$. To emphasize that a #n[proposition] is viewed as a class, we write ${dv(x) mid(|) rP(rx, rv(a_1), dots, rv(a_n))}$. We will use usual $defeq$-notation for classes, too.
]
#let classcompr(x,P) = ${dv(#x) #link(<class>,$mid(|)$) #P}$
#names(<class>,"class","classes")
Lots of constructions that go through with #n[sets] also work with #n[classes], as long as they do not require collecting subsets. We will expect the reader to handle this implicitly unless noted otherwise, since the cases where this is used are relatively simple.
#remark(title: [Sets as classes])[
  #n[Sets] can be viewed as certain #n[classes]: If $dv(x)$ is a #n[set], $classcompr(y, ry mem rx)$ is a #n[class] such that #n[for all] $dv(y)$, $ry mem rx iff ry mem classcompr(y, ry mem rx)$. We will use this conversion implicitly when needed. Clearly, if a #n[class] arises from two #n[sets], they must be #n[equal] by the axiom of #n[extensionality]. Hence a #n[class] that is proven arise from a #n[set] suffices to define that #n[set].
]<set.to-class>

#definition(title: "Proper class")[
  A #def(<class.proper>)[proper class] is a #n[class] $dv(A)$ that does not arise from a #n[set] in the #lk(<set.to-class>)[above way], i.e. there does not #n[exist] any #n[set] $dv(x)$ such that #n[for all] #n[sets] $dv(y)$, $ry mem rx iff ry mem rA$.
]

#names(<class.proper>, "proper class", "proper classes")
#example(title: "Russell's paradox")[
  It is not immediately clear that there are any #n[proper classes]. But let us define $dv(R) defeq classcompr(x, dv(x) nmem dv(x))$. If $rR$ were not #lk(<class.proper>)[proper], there would be a #n[set] $dv(r)$ with $dv(x) mem rr iff rx nmem rx$. Hence $das(1,rr mem rr iff rr nmem rr)$. With #n[excluded middle], it is very easy to derive a #n[contradiction], but let us work around it:

  We have $das(3,rr nmem rr)$: If $das(2,rr mem rr)$, $rr nmem rr$ follows#justifytas(1), hence $fls$.
  Now again by assumption#justifytas(1,3), this also means we have $das(4,rr mem rr)$, #n[contradiction] #justifytas(3,4).

  So such a #n[set] cannot #n[exist] even intutitionistically.
]
=== Constructing basic sets
==== Pairing
#axiom(title: "Axiom of pairing")[
  For #n[all] #n[sets] $dv(x),dv(y)$, the #n[class] $classcompr(a, a = x disj a = y)$ is a #n[set].
]<set.ax-pairing>
#let upair(x,y) = $#link(<unordered-pair>,${$)#x,#y#link(<unordered-pair>,$}$)$
#let singleton(x) = $#link(<set.singleton>,${$)#x#link(<set.singleton>,$}$)$
#definition(title: "Unordered pair")[
  For #n[all] #n[sets] $dv(x),dv(y)$, define the #n[set] we call their #def(<unordered-pair>)[unordered pair] as $ {rx,ry} defeq classcompr(a, ra = rx disj ra = ry). $ Also define the #def(<set.singleton>)[singleton #n[set]] ${rx}$ containining $rx$ as $upair(rx,rx)$.
]
#names(<unordered-pair>, plural: true, "unordered pair")
#names(<set.singleton>, "singleton")
#proof(title: "Proof of well-definedness")[
  #n[For any] #n[sets] $dv(x), dv(y)$, $upair(x,y)$ is a #n[set] due to the #lk(<set.ax-pairing>)[axiom of pairing]. It is unique since it is defined by a #n[class]#justifyt(<set.to-class>). This also implies the well-definedness of $singleton(x)$. 
]
#proposition(title: "Pairs and singletons")[
  Let $dv(a), dv(w), dv(x),dv(y), dv(z)$ be #n[sets]. Then, the following hold:
  + $ra mem upair(rx,ry) iff ra = rx disj ra = ry$, <unordered-pair.mem-iff>
  + $ra mem singleton(rx) iff ra = rx$, <set.singleton.mem-iff>
  + $singleton(rx) = singleton(ry) iff rx = ry$, <set.singleton-eq-singleton>
  + $rx = ry iff forall(v) rx mem rv(v) iff ry mem rv(v)$, <set.eq-iff-mem-same>
  + $upair(rw,rx) = upair(ry,rz) iff (rw = ry conj rx = rz) disj (rw = rz conj rx = ry)$, <unordered-pair.eq-unordered-pair>
  + $upair(rx,ry) = upair(ry,rx)$. <unordered-pair.comm>
]
#proof[
  + By #lk(<unordered-pair>)[definition].
  + Compare
    $ra mem singleton(rx) #justify(<set.singleton>, iff) ra mem upair(rx, rx) #justify(<set.singleton>, iff) ra = rx disj ra = rx #justify(<or.self>, iff) a = x.$
  + The right-to-left-direction is obvious from #lk(<eq.subst>)[substitution]. Now let $singleton(rx) = singleton(ry)$. Then by #lk(<eq.subst>)[substitution] $rx mem singleton(rx) iff rx mem singleton(ry)$. From #lk(<set.singleton.mem-iff>)[the previous], this can be rewritten to $rx = rx iff rx = ry$, hence#justifyt(<eq.refl>) $rx = ry$.
  + Left-to-right is clear. Now assume $forall(v) rx mem rv(v) iff ry mem rv(v)$. Choose $dv(v) := singleton(ry)$. Hence 
    $rx mem singleton(ry) iff ry mem singleton(ry)$, so #lk(<set.singleton.mem-iff>)[from the previous], $rx = ry iff ry = ry$ and $rx = ry$ follows#justifyt(<eq.refl>).
  + We show both directions.
    + Assume $upair(rw,rx) = upair(ry,rz)$.
      Then#justifyt(<unordered-pair.mem-iff>) we have $rw mem upair(ry,rz) iff rw = ry disj rw = rz$ and similarly
      $rx = ry disj rx = rz$. We need to exclude the two cases
      $rw = ry conj rx = ry, rw = rz conj rx = rz$.

      If $rw = ry = rx$, from $upair(rw,rx) = upair(ry,rz)$ we know that $rz mem upair(rw,rx)$ hence $rz = rw disj rz = rx = rw$. Thus $rw = rx = ry = rz$ and the #n[disjunction] also holds. Similar reasoning for the case $rw = rz = rx$.
    + First, assume $rw = ry, rx = rz$. Then for any #n[set] $dv(a)$,
      $ ra in upair(rw,rx) #justify(<unordered-pair.mem-iff>,iff) ra = rw disj ra = rx #justify(<eq.trans>,iff) ra = ry disj ra = rz #justify(<unordered-pair.mem-iff>,iff) ra in upair(ry,rz). $
      Now, assume $rw = rz, rx = ry$. Then for any #n[set] $dv(a)$,
      $ ra in upair(rw,rx) #justify(<unordered-pair.mem-iff>,iff) ra = rw disj ra = rx #justify(<eq.trans>,iff) ra = rz disj ra = ry #justify(<or.comm>,iff) ra = ry disj ra = rz#justify(<unordered-pair.mem-iff>,iff) ra in upair(ry,rz). $
      In both cases, use #n[extensionality] to conclude $upair(rw,rx) = upair(ry,rz)$.
  + Apply the #lk(<unordered-pair.eq-unordered-pair>)[previous proposition]. Then it suffices to show that $rx = ry conj rx = ry$, which is clear.
  ]
#let pair(x,y) = $#link(<pair>,$($)#x,#y#link(<pair>,$)$)$
#let tuple(..args) = $#link(<tuple>,$($) #args.pos().join([, ])#link(<tuple>,$)$)$
#definition(title: "Ordered pairs and tuples")[
  Let $dv(x),dv(y)$ be #n[sets]. Then, we define the #def(<pair>)[ordered pair] (or just _pair_) of $rx, ry$ as 
  $ (rx,ry) defeq upair(singleton(rx), upair(rx,ry)). $
  If we are given #n[sets] $dv(x)_dv(i)$ for $1 <= ri <= dv(n)$, then
  we metamathematically define #def(<tuple>)[tuples]
  $ (dv(x)_1, dots, rx_(rn-1), rx_rn) defeq pair((rx_1, dots, rx_(rn-1)), rx_rn) $ 
  for all numbers $rn >= 3$.
]
#names(<pair>, plural:true, "pair", "ordered pair")
#names(<tuple>, plural:true, "tuple", "ordered tuple", "triple", "ordered triple")
#lemma(title: [Equality of ordered pairs])[
  #n[For all] #n[sets] $dv(w),dv(x),dv(y),dv(z)$ we have 
  $ pair(rw,rx) = pair(ry,rz) iff rw = ry conj rx = rz. $ <pair.eq-pair>
  Immediately, this #n[implies] that for #n[sets] $dv(x)_dv(i), dv(y)_dv(j)$ for $1 <= ri, rj <= dv(n)$, we have 
  $  tuple(rx_1, dots, rx_n) = tuple(ry_1, dots, ry_n) iff rx_1 = ry_1 conj dots conj rx_n = ry_n. $ <tuple.eq-tuple>
]
#proof[
  The right-to-left #n[implication] is clear.
  So assume
  $ pair(rw,rx) = upair(singleton(rw), upair(rw,rx)) = upair(singleton(ry), upair(ry,rz)) = pair(ry,rz). $
  Then, as #lk(<unordered-pair.eq-unordered-pair>)[shown above], there are two cases to cover:
  + $singleton(rw) = singleton(ry) #justify(<set.singleton-eq-singleton>,iff) rw = ry, upair(rw,rx) = upair(ry,rz)$: Then, as #lk(<unordered-pair.eq-unordered-pair>)[shown above], either $rw = ry, rx = rz$ or $rw = rz, rx = ry$. The first case amounts to precisely what we want to show, the second case implies $rw=rx=ry=rz$ hence $rw = ry, rx = rz$.
  + $singleton(rw) = upair(ry,rz), upair(rw,rx) = singleton(ry)$:
    Then#justifyt(<set.singleton.mem-iff>) $ry = rw, rz = rw, rw = ry, rx = ry$ such that $rw = ry$, $rx = rz$ as required.
]
#remark[
  This is the first instance of a common phenomenon in mathematics where a concrete construction of an object is irrelevant to its usage and what matters instead are properties that define its behavior more or less uniquely.

  For example it does not matter that a #n[ordered pair] of $dv(x),dv(y)$ is defined as $upair(singleton(rx), upair(rx,ry))$ and indeed, we will almost never see that #n[term] again. What we care about instead is that we _can_ always construct an #n[ordered pair] and that it is already determined by its two components.
]

==== Union 
#axiom(title: [Axiom of unions])[
  For #n[every] #n[set] $dv(x)$, the #n[class] $classcompr(a, exists(y) ry mem rx conj ra mem ry)$ is a #n[set].
]<set.ax-union>
#let setUnion(a) = link(<set.Union>)[$union.big #a$]
#definition(title: "Union of a set")[
  For #n[every] #n[set] $dv(x)$, define the #n[set] we call its #def(<set.Union>)[union] as $ setUnion(rx) defeq classcompr(a, exists(y) ry mem rx conj ra mem ry). $
]
#names(<set.Union>, "union of a set", "union.set")
#proof(title: "Proof of well-definedness")[Well-defined due to the #lk(<set.ax-union>)[axiom of unions].]
#let union = link(<set.union>)[$union$]
#definition(title: "Union of two sets")[
  For #n[all] #n[sets] $dv(x), dv(y)$, define the #n[set] we call their #def(<set.union>)[union] (or _binary union_) as $ rx union ry defeq setUnion(upair(rx,ry)). $
]
#names(<set.union>, "binary union", "union")
#proposition(title: [Membership in a binary union])[
  Let $dv(x), dv(y), dv(a)$ be #n[sets]. Then $ ra mem rx union ry iff (ra mem rx disj ra mem ry). $
]<set.union.mem-iff>
#proof[
  $ ra mem rx union ry &#justify(<set.union>,iff) ra mem setUnion(upair(rx,ry))
    \ &#justify(<set.Union>,iff) exists(z) rz mem upair(rx,ry) conj ra mem rz 
    \ &#justify(<unordered-pair.mem-iff>,iff) exists(z) (rz = rx disj rz = ry) conj ra mem rz 
    \ &#justify(<exists.or>,iff)#justifyt(<and.or-distr>) ra mem rx disj ra mem ry.
    $
]
==== Separation
#let compr(x,A,P) = ${dv(#x) mem #A #link(<set.separation>,$mid(|)$) #P}$
#let compr1(x,P) = ${dv(#x) #link(<set.separation>,$mid(|)$) #P}$

#axiom(title: [Axiom schema of separation])[
  Let $dv(x)$ be a #n[set] and $dv(P)(a)$ a #n[proposition]. Then, the #n[class] $ classcompr(a,ra mem rx conj P(ra)) $ is a #n[set].
]<set.ax-separation>
#definition(title: [Separation])[
  Let $dv(x)$ be a #n[set] and $dv(P)(a)$ a #n[proposition]. Then, we define the #def(<set.separation>)[set given by separation by $rP$ from $rx$] as 
  $ compr1(a,ra mem rx conj rP(rx)) defeq compr(a,rx, rP(rx)) defeq classcompr(a, ra mem rx conj rP(rx)) $
]
#names(<set.separation>, "separation", "comprehension")
#proposition(title: [Separation properties])[
  For all #n[propositions] $dv(P)(x)$ that define a #n[set] and any other ones $dv(Q)(x)$ as well as a #n[set] $dv(x)$, we have 
  + $compr(a,compr1(a, rP(ra)), rQ(ra)) = compr1(a, rP(ra) conj rQ(ra))$, <set.separation.assoc>
  + $compr1(a, ra mem rx) = rx$ <set.separation-mem>.
]
#proof[
  + Follows#justifyt(<set.ext>) from 
    $ dv(b) mem compr(a,compr1(a, rP(ra)), rQ(ra)) iff  b mem compr1(a, rP(ra)) conj rQ(rb) iff rP(rb) conj rQ(rb) iff rb mem compr1(a, rP(ra) conj rQ(ra)). $
  + Follows immediately from #n[extensionality].
]
#let emptyset = $#link(<set.empty>)[$emptyset$]$
#definition(title: [Empty set])[
  Let $dv(x)$ be #n[any] #n[set]. Then, we define the #def(<set.empty>)[empty set] as 
  $ emptyset defeq compr(a,rx, fls). $
  A #n[set] is _empty_ iff it is #n[equal] to $emptyset$ and #def(<set.nonempty>)[nonempty] #n[iff] it is #n[not].
]
#proof(title: "Justification")[
  The definition is independent of $rx$:
  $ b mem emptyset #justify(<set.empty>,iff) b mem compr(a,rx, fls) #justify(<set.separation>, iff) (b mem a conj fls) #justify(<and.true-false>, iff) fls $
]
#names(<set.empty>, "empty", "empty set")
#names(<set.nonempty>, "nonempty", "nonempty set","not empty")
#proposition(title: "Properties of the empty set")[
  For #n[all] #n[sets] $dv(x)$, we have the following:
  + $rx nmem emptyset$, <set.empty.nmem>
  + $rx$ is #n[empty] #n[iff] $forall(a) ra nmem rx$, <set.empty.iff>
  + $rx$ is #n[nonempty] #n[iff] there is an $dv(a) mem rx$. <set.nonempty-iff>
]
#proof[
  + By #lk(<set.empty>)[definition], $rx mem emptyset$ #n[implies] $fls$.
  + Left-to-right follows from #lk(<set.empty.nmem>)[the previous part]. So assume $forall(a) ra nmem rx$.
    Then, $ forall(a) ra mem rx imp fls #justify(<false.elim>,iff) iff forall(a) ra mem rx iff fls #justify(<set.empty.iff>, iff) forall(a) ra mem rx iff ra mem emptyset. $
  + $rx$ is #n[nonempty] #n[iff] it is #n[not] #n[empty], e.g. 
    $neg forall(a) ra nmem rx #justify(<exists.not-all>, iff)#justifyt(<not.not-iff>) exists(a) ra mem rx$.
]

#definition(title: [Sets of given elements])[
  For #n[all] #n[sets] $dv(x)_1, dots, rx_dv(n)$ (metamathematically quantifying over $rn$), we define the #def(<set.finite-list>)[set given by enumeration of elements] ${rx_1, dots, rx_rn}$:
  - for $rn = 0$, set ${rx_1, dots, rx_rn} defeq emptyset$,
  - otherwise, ${rx_1,dots,rx_rn} defeq {rx_1,dots,rx_(rn-1)} union singleton(rx_rn).$
]
#remark[
  For $rn = 2$, this clashes with the notation for #n[unordered pairs], but we will see that the denoted #n[sets] agree so it cannot cause any issues.
]
#names(<set.finite-list>, "set given by the elements")
#let finset(..args) = $#link(<set.finite-list>,${$) #args.pos().join([, ])#link(<set.finite-list>,$}$)$

#proposition(title: [Membership in set of given elements])[
  For #n[all] #n[sets] $dv(a),dv(x)_1, dots, rx_dv(n)$, we have 
  $ ra mem finset(rx_1, dots, rx_rn) iff ra = rx_1 disj dots disj ra = rx_rn. $
]<set.finite-list.mem-iff>
#proof[
  By metamathematical induction on $rn$:
  + For $rn=0$, we need#justifyt(<set.finite-list>) to show $ra mem emptyset iff fls$. But this is clear.#justifyt(<set.empty.nmem>).
  + For $rn > 0$, we need#justifyt(<set.finite-list>) to show 
  $ ra mem finset(rx_1,dots,rx_(rn-1)) union singleton(rx_rn) iff ra = rx_1 disj dots disj ra = rx_rn. $
  So consider the induction hypothesis $das(1, ra mem finset(rx_1, dots, rx_(rn-1)) iff ra = rx_1 disj dots disj ra = rx_(rn-1))$: Then, we have
   $ ra mem finset(rx_1,dots,rx_(rn-1)) union singleton(rx_rn) &#justify(<set.union.mem-iff>, iff) ra mem finset(rx_1,dots,rx_(rn-1)) disj ra mem singleton(rx_rn)
   \ #justifytas1(1)&#justify(<set.singleton.mem-iff>, iff) (ra = rx_1 disj dots disj ra = rx_(rn-1)) disj ra = rx_rn
   \ &#justify(<or.assoc>,iff)
   ra = rx_1 disj dots disj ra = rx_rn. $
]
==== Intersections
#let setIntersection(a) = link(<set.Intersection>)[$inter.big #a$]
#definition(title: "Intersection of a set")[
  For #n[every] #n[nonempty] #n[set] $dv(x)$ with #n[element] $dv(c)$, define the #n[set] we call its #def(<set.Intersection>)[intersection] as $ setIntersection(rx) defeq compr(a, rc, forall(y) ry mem rx imp ra mem ry). $ If $dv(x)$ is #n[empty], depending on context $setIntersection(x)$ may be defined as the "surrounding universe".
]
#names(<set.Intersection>, "intersection of a set", "intersection.set")
#proposition(title: [Membership in a binary union])[
  Let $dv(x)$ be a #n[nonempty] #n[set] with #n[element] $dv(c)$. Then #n[for all] $dv(a)$, $ ra mem setIntersection(rx) iff (forall(b) rb mem rx imp ra mem rb) $
]<set.Intersection.mem-iff>
#proof[
  We have#justifyt(<set.Intersection>)
  $ ra mem setIntersection(rx) &iff (ra mem rc conj forall(b) rb mem rx imp ra mem rb) \ &iff ((rc mem rx imp ra mem rc) conj forall(b) rb mem rx imp ra mem rb) \ &iff forall(b) rb mem rx imp ra mem rb. $
]

#let inter = link(<set.inter>)[$inter$]
#definition(title: "Intersection of two sets")[
  For #n[all] #n[sets] $dv(x), dv(y)$, define the #n[set] we call their #def(<set.inter>)[intersection] (or _binary intersection_) as $ rx inter ry defeq setIntersection(upair(rx,ry)). $
]
#names(<set.inter>, "binary intersection", "intersection")
#proposition(title: [Membership in a binary intersection])[
  Let $dv(x), dv(y), dv(a)$ be #n[sets]. Then $ ra mem rx inter ry iff (ra mem rx conj ra mem ry). $
]<set.inter.mem-iff>
#proof[
  $ ra mem rx inter ry &#justify(<set.inter>,iff) ra mem setIntersection(upair(rx,ry))
    \ &#justify(<set.Intersection>,iff) forall(z) rz mem upair(rx,ry) imp ra mem rz 
    \ &#justify(<unordered-pair.mem-iff>,iff) forall(z) (rz = rx disj rz = ry) imp ra mem rz 
    \ &#justify(<or.elim>,iff) forall(z) (rz = rx imp ra mem rz) conj (rz = ry imp ra mem rz) 
    \ &#justify(<all.and>,iff)ra mem rx conj ra mem ry.
    $
]
#proposition(title: [Properties of union and intersection])[
  For all #n[sets] $dv(x), dv(y), dv(z)$ we have
  + $rx union rx = rx$<set.union.self>, $rx inter rx = rx$<set.inter.self>,
  + $rx union ry = ry union rx$<set.union.comm>, $rx inter ry = ry inter rx$<set.inter.comm>,
  + $rx union (ry union rz) = (rx union ry) union rz$<set.union.assoc>, $rx inter (ry inter rz) = (rx inter ry) inter rz$<set.inter.assoc>,
  + $rx union (ry inter rz) = (rx union ry) inter (rx union rz)$<set.union.inter-distr>, $rx inter (ry union rz) = (rx inter ry) union (rx inter rz)$<set.inter.union-distr>,
  + $rx union (rx inter ry) = rx$<set.union.inter-absorb>, $rx inter (rx union ry) = rx$<set.inter.union-absorb>,
  + $rx union emptyset = rx$<set.union.empty>.
]
#proof[
  Use #n[extensionality] and the following #n[biconditionals]:
  + Idempotency of #lk(<or.self>)[or], #lk(<and.self>)[and],
  + commutativity of #lk(<or.comm>)[or], #lk(<and.comm>)[and],
  + associativity of #lk(<or.assoc>)[or], #lk(<and.assoc>)[and],  
  + distributivity of #lk(<or.and-distr>)[or over and], #lk(<and.or-distr>)[and over or],  
  + absorption of #lk(<or.and-absorb>)[or over and], #lk(<and.or-absorb>)[and over or],
  + #n[disjunction] with #n[absurdity] #justifyt(<or.true-false>).]

We try to save most facts about the "big operators" for later when we introduce them for families of #n[sets], which tends to be the substantially more common mode of usage in mathematical practice.

==== Subsets
#let ssubset = $#link(<ssubset>,$subset.neq$)$
#let subset = $#link(<subset>,$subset.eq$)$
#definition(title: "Subsets")[
  Let $dv(x),dv(y)$ be #n[sets]. Then, we set 
  $ rx subset ry &defiff (forall(a) ra mem rx imp ra mem ry), \
    rx ssubset ry &defiff rx subset ry conj rx neq ry.
   $
The former we read as "$rx$ is a #def(<subset>)[subset] of $ry$", the latter as "$rx$ is a #def(<ssubset>)[strict subset] of $ry$".
]
#names(<subset>, "subset", "subsets", "included", "part")
#names(<ssubset>, "strict subset", "proper subset")
#proposition(title: "Basic subset properties")[
  #n[For any] #n[sets] $dv(x), dv(y), dv(z)$ we have the following:
  + $rx subset rx$<subset.refl>,
  + $rx subset ry imp ry subset rx imp rx = ry$<subset.antisymm>,
  + $ry subset rz imp rx subset ry imp rx subset rz$<subset.trans>,
  + $rx ssubset ry iff (rx subset ry conj neg (ry subset rx)) iff (rx subset ry conj exists(a) a mem ry conj a nmem rx)$<ssubset.iff-subset-not-subset>,
  + $neg rx ssubset rx$<ssubset.irrefl>,
  + $rx ssubset ry imp neg ry subset rx$<ssubset.asymm-subset>,
  + $rx ssubset ry imp neg ry ssubset rx$<ssubset.asymm>,
  + $ry ssubset rz imp rx subset ry imp rx ssubset rz$<ssubset.trans-subset-right>,
  + $ry subset rz imp rx ssubset ry imp rx ssubset rz$<ssubset.trans-subset-left>,
  + $ry ssubset rz imp rx ssubset ry imp rx ssubset rz$<ssubset.trans>,
  + $emptyset subset rx$<set.empty.subset>,
  + $rx subset emptyset iff rx = emptyset$<set.empty.eq-iff-subset>.
]
#proof[
  + We need to show $forall(a) ra mem rx imp ra mem rx$, but that is trivial.
  + From #n[extensionality]: For #n[any] $dv(a)$ we need to show $ra mem rx iff ra mem ry$. But $ra mem rx imp ra mem ry$ follows from $rx subset ry$, and $ra mem ry imp ra mem rx$ follows from $ry subset rx$#justifyt(<subset>)#justifyt(<all.elim>).
  + Assume $dv(a) mem rx$. Then from $rx subset ry$ we know#justifyt(<subset>) $ra mem ry$ and from $ry subset rz$ we know $ra mem rz$.
  + We show $1 imp 2 imp 3 imp 1$.
    + Assume $rx ssubset ry$. Then $rx subset ry$ follows from #lk(<ssubset>)[definition]. Now if $ry subset rx$ were true, by the shown #lk(<subset.antisymm>)[antisymmetry] we would have $rx = ry$ in contradiction to $rx neq ry$.
    + Assume $rx subset ry, not (ry subset rx)$. It remains to be shown that there #n[exists] some $dv(a)$ with $ra mem ry, ra nmem rx$. If that were not true, every $dv(a)$ with $ra mem ry$ would fulfill $ra mem rx$ and $ry subset rx$, #n[contradiction].
    + Assume $rx subset ry$ and $dv(a) mem ry, ra nmem rx$. We have to show $rx subset ry$ (clear) and $rx neq ry$. But if $rx = ry$, we would have $ra mem ry = rx$, #n[contradiction].
  + Assume $rx ssubset rx$. Then in particular, $rx neq rx$, in #n[contradiction] to #lk(<eq.refl>)[reflexivity].
  + Assume $rx ssubset ry, ry subset rx$. Then, $rx subset ry, ry subset rx$ so due to #lk(<subset.antisymm>)[antisymmetry] we have $rx = ry$, in #n[contradiction] due to $rx neq ry$ following from $rx ssubset ry$.
  + Follows from #lk(<ssubset.asymm-subset>)[the above] due to $rx ssubset ry imp rx subset ry$.
  + Assume $ry ssubset rz, rx subset ry$. We need to show $rx subset rz$, $rx neq rz$. The former follows from $ry subset rz, rx subset ry$ which we know from our assumptions.#justifyt(<ssubset>) Now let $rx = rz$. Then $rx subset ry ssubset rx$, which #lk(<ssubset.asymm-subset>)[we know] cannot hold. #n[Contradiction].
  + Assume $ry subset rz, rx ssubset ry$. We need to show $rx subset rz$, $rx neq rz$. The former follows from $ry subset rz, rx subset ry$ which we know from our assumptions.#justifyt(<ssubset>) Now let $rx = rz$. Then $ry subset rx ssubset ry$, which #lk(<ssubset.asymm-subset>)[we know] cannot hold. #n[Contradiction].
  + Assume $ry ssubset rz, rx ssubset ry$. Then we have $rx subset ry$ and from the #lk(<ssubset.trans-subset-left>)[above] we can see $rx ssubset rz$.
  + Assume $dv(a) mem emptyset$. #n[Contradiction].
  + Right-to-left follows from #lk(<subset.refl>)[reflexivity], left-to-right from #lk(<subset.antisymm>)[antisymmetry] and the #lk(<set.empty.subset>)[previous statement].
]
#proposition(title: "Subsets and operations")[
  #n[For any] #n[sets] $dv(x), dv(y), dv(z)$ we have the following:
  + $rx subset rx union ry, ry subset rx union ry$<set.union.subset>,
  + $rx inter ry subset rx, rx inter ry subset ry$<set.inter.subset>,
  + $rx subset ry imp rx union rz subset ry union rz$<set.union.mono>,
  + $rx subset ry imp rx inter rz subset ry inter rz$<set.inter.mono>,
  + $rx subset ry iff rx union ry = ry$<set.union.eq-iff-subset>,
  + $rx subset ry iff rx inter ry = rx$<set.inter.eq-iff-subset>,
  + $rx subset ry imp setUnion(rx) subset setUnion(ry)$<set.Union.mono>,
  + $rx subset ry imp setIntersection(ry) subset setIntersection(rx)$<set.Inter.mono> for #n[nonempty] $rx,ry$.
]
#proof[
  + $ dv(a) mem rx &#justify(<or.intro>,imp) ra mem rx disj ra mem ry #justify(<set.union.mem-iff>,iff) ra mem rx union ry, \
  dv(a) mem ry &#justify(<or.intro>,imp) ra mem rx disj ra mem ry #justify(<set.union.mem-iff>,iff) ra mem rx union ry. $ 
  + $ dv(a) mem rx inter ry &#justify(<set.inter.mem-iff>,iff) ra mem rx conj ra mem ry #justify(<and.elim>,imp) ra mem rx, \
  dv(a) mem rx inter ry &#justify(<set.inter.mem-iff>,iff) ra mem rx conj ra mem ry #justify(<and.elim>,imp) ra mem ry. $
  + Assume $rx subset ry$. Then 
   $ dv(a) mem rx union rz #justify(<set.union.mem-iff>,iff) ra mem rx disj ra mem rz #justify(<or.map>, imp) ra mem ry disj ra mem rz #justify(<set.union.mem-iff>,iff) ra mem ry union rz. $
  + Assume $rx subset ry$. Then 
   $ dv(a) mem rx inter rz #justify(<set.inter.mem-iff>,iff) ra mem rx conj ra mem rz #justify(<and.map>, imp) ra mem ry conj ra mem rz #justify(<set.inter.mem-iff>,iff) ra mem ry inter rz. $
  + First assume $rx subset ry$.    
    From #lk(<set.union.subset>)[a previous statement] and #lk(<subset.antisymm>)[antisymmetry], it suffices to prove $rx union ry subset ry$. But by #lk(<set.union.mono>)[monotony], we have $rx union ry subset ry union ry #justify(<set.union.self>, $=$) ry$. Now assume $rx union ry = ry$. Then, $rx #justify(<set.union.subset>,subset) rx union ry = ry$.
  + First assume $rx subset ry$. From #lk(<set.inter.subset>)[a previous statement] and #lk(<subset.antisymm>)[antisymmetry], it suffices to prove $rx subset rx inter ry$. But by #lk(<set.union.mono>)[monotony], we have $rx inter rx #justify(<set.inter.self>, $=$) rx subset rx inter ry$. Now assume $rx inter ry = ry$. Then $ry = rx inter ry #justify(<set.inter.subset>,subset) rx$.
  + Let $rx subset ry$ and $dv(a) mem setUnion(rx)$, i.e.#justifyt(<set.Union>) $ra mem dv(b) mem rx$. Then $rb mem ry$, hence#justifyt(<set.Union>) $ra mem setUnion(ry)$.
  + Let $rx subset ry$ and $dv(a) mem setIntersection(ry)$, i.e.#justifyt(<set.Intersection.mem-iff>) $forall(b) rb mem ry imp ra mem rb$. We need to show#justifyt(<set.Intersection.mem-iff>) $forall(b) rb mem rx imp ra mem rb$. But for #n[any] $dv(b)$, $rb mem rx$ #n[implies] $rb mem ry$ such that $ra mem rb$.    
]
==== Set differences
#let without = link(<set.difference>,$without$)
#definition(title: "Set difference")[
  Let $dv(x), dv(y)$ be #n[sets]. Then, the #def(<set.difference>)[difference set] $rx without ry$ is defined as 
  $ rx without ry defeq compr(a,rx,ra nmem ry). $
]
#names(<set.difference>, plural: true, "difference set", "set difference", "relative complement")
#proposition(title: "Set difference properties")[
  #n[For all] #n[sets] $dv(x), dv(y), dv(z)$, we have 
  + $rx without ry = emptyset iff rx subset ry$<set.difference.empty-iff>,
  + $rx without rx = emptyset$<set.difference.self>,
  + $emptyset without rx = emptyset$<set.difference.empty-left>,
  + $rx without ry subset rx$<set.difference.subset>,
  + $rx inter ry = emptyset iff rx without ry = rx$<set.difference.empty-iff-disjoint>,
  + $rx subset ry imp rx without rz subset ry without rz$<set.difference.mono>,
  + $rx subset ry imp rz without ry subset rz without rx$<set.difference.anti>,
  + $rx without (ry union rz) = (rx without ry) inter (rx without rz) =(rx without ry) without rz$<set.difference.union-right>,
  + $rx without (ry inter rz) = (rx without ry) union (rx without rz)$<set.difference.inter-right>,
  + $(rx union ry) without rz = (rx without rz) union (ry without rz)$<set.difference.union-left>,
  + $(rx inter ry) without rz = (rx without rz) inter (ry without rz)$<set.difference.inter-left>,
  + $rx without (ry without rx) = rx$<set.difference.difference>,
  + $rx inter (ry without rz) = (rx inter ry) without (rx inter rz) = (rx inter ry) without rz$<set.inter.difference>,
  + $rx union (ry without rz) = (rx union ry) without (rz without rx) = (rx union ry) without ((ry inter rz) without rx)$<set.union.difference>,
  + $(rx without ry) union (rx inter ry) = rx, (rx without ry) inter (rx inter ry) = emptyset$<set.difference.disjoint-decomp>]
#proof[
  + If $rx without ry = emptyset$, we have#justifyt(<set.difference>) $neg(dv(a) mem rx conj ra nmem ry)$. Hence $ra mem rx imp ra mem ry$.
   Similarly, #n[if] $rx subset ry$ and $dv(a) mem rx without ry$, we have#justifyt(<set.difference>) $ra mem rx, ra nmem ry$, but by assumption#justifyt(<subset>) $ra mem ry$, #n[contradiction].
   So#justifyt(<set.empty.iff>) $rx without ry = emptyset$.
  + Follows from #lk(<set.difference.empty-iff>)[the previous] and #lk(<subset.refl>)[reflexivity].
 + Follows from #lk(<set.difference.empty-iff>)[the previous] and the #n[empty set] being a #n[subset] of #n[every] #n[set]#justifyt(<set.empty.subset>).
 + $ dv(a) mem rx without ry #justify(<set.difference>, iff) ra mem rx conj ra nmem ry #justify(<and.elim>,imp) ra mem rx. $
+ First, assume $rx inter ry = emptyset$. From #lk(<set.difference.subset>)[the previous] and #lk(<subset.antisymm>)[antisymmetry], we only have to show $rx subset rx without ry$. So let $dv(a) mem rx$ and assume $ra mem ry$. Then $ra mem rx inter ry$#justifyt(<set.inter.mem-iff>), #n[contradiction]. Hence $ra nmem ry$ and $ra mem rx without ry$.
 
 Now assume $rx without ry = rx$ and $ra mem rx inter ry$. Then#justifyt(<set.inter.subset>) $ra mem rx = rx without ry$, hence#justifyt(<set.difference>) $ra nmem ry$, which is in #n[contradiction] to $ra mem rx inter ry$#justifyt(<set.inter.subset>).
+ Assume $rx subset ry$, $dv(a) mem rx without rz$. Then#justifyt(<set.difference>) $ra mem rx, ra nmem rz$, hence $ra mem ry, ra nmem rz$ so $ra mem ry without rz$#justifyt(<set.difference>).
+ Assume $rx subset ry$, $dv(a) mem rz without ry$. Then $ra mem rz, ra nmem ry$#justifyt(<set.difference>). From $rx subset ry$ we have $ra nmem rx$#justifyt(<imp.converse>), hence $ra mem rz without rx$#justifyt(<set.difference>).
+ $ dv(a) mem rx without (ry union rz) &#justify(<set.difference>, iff)#justifyt(<set.union.mem-iff>) ra mem rx conj neg (ra mem ry disj ra mem rz) \
  & #justify(<not.or>, iff) ra mem rx conj ra nmem ry conj ra nmem rz \ &
  #justify(<and.self>, iff) (ra mem rx conj ra nmem ry) conj (ra mem rx conj ra nmem rz)
  \ & #justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>) ra mem (rx without ry) inter (rx without rz) $
  and 
  $ ra mem rx conj ra nmem ry conj ra nmem rz &iff (ra mem rx conj ra nmem ry) conj ra nmem rz \&#justify(<set.difference>,iff) ra mem rx without ry conj ra nmem rz
  \ &#justify(<set.difference>,iff) ra mem (rx without ry) without rz. $
  Now (as well as in the forthcoming proofs) use #n[extensionality].
+ $ dv(a) mem rx without (ry inter rz) &#justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>) ra mem rx conj neg (ra mem ry conj ra mem rz) \
  & #justify(<not.and>, iff) ra mem rx conj (ra nmem ry disj ra nmem rz)
  \ &#justify(<and.or-distr>, iff) (ra mem rx conj ra nmem ry) disj (ra mem rx conj ra nmem rz)
     \ & #justify(<set.difference>, iff)#justifyt(<set.union.mem-iff>) ra mem (rx without ry) union (rx without rz). $
+ $ dv(a) mem (rx union ry) without rz &#justify(<set.difference>, iff)#justifyt(<set.union.mem-iff>) (ra mem rx disj ra mem ry) conj ra nmem rz
\ &#justify(<and.or-distr>, iff) (ra mem rx conj ra nmem rz) disj (ra mem ry conj ra nmem rz) \ &#justify(<set.difference>, iff)#justifyt(<set.union.mem-iff>) ra mem (rx without rz) union (ry without rz). $
+ $ dv(a) mem (rx inter ry) without rz &#justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>) (ra mem rx conj ra mem ry) conj ra nmem rz
\ &#justify(<and.self>, iff) (ra mem rx conj ra nmem rz) conj (ra mem ry conj ra nmem rz) \ &#justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>) ra mem (rx without rz) conj (ry without rz). $
+ $ dv(a) mem rx without (ry without rx) &#justify(<set.difference>, iff) ra mem rx conj neg (ra mem ry conj neg ra mem rx)
\ &#justify(<not.and>, iff)#justifyt(<not.not-iff>) ra mem rx conj (neg ra mem ry disj ra mem rx)\ 
&#justify(<and.or-absorb>, iff) ra mem rx.
$
+ $ dv(a) mem rx inter (ry without rz) &#justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>) ra mem rx conj ra mem ry conj ra nmem rz
\ &#justify(<and.or-absorb>, iff) (ra mem rx conj ra mem ry) conj (ra nmem rx disj ra nmem rz)
\ &#justify(<not.and>, iff)#justifyt(<set.inter.mem-iff>) (ra mem rx conj ra mem ry) conj ra nmem (rx inter rz)
\ &#justify(<set.difference>, iff)#justifyt(<set.inter.mem-iff>)
ra mem (rx inter ry) without (rx inter rz)
$
  and 
  $ ra mem rx conj ra mem ry conj ra nmem rz &#justify(<set.inter.mem-iff>, iff) ra mem (rx inter ry) conj ra nmem rz \ &#justify(<set.difference>, iff) ra mem ((rx inter ry) without rz). $
+ $ dv(a) mem rx union (ry without rz) &#justify(<set.difference>, iff)#justifyt(<set.union.mem-iff>) ra mem rx disj (ra mem ry conj ra nmem rz) 
\ &#justify(<or.and-distr>, iff) (ra mem rx disj ra mem ry) conj (ra mem rx disj ra nmem rz)
\ &#justify(<set.union.mem-iff>, iff)#justifyt(<not.and>) (ra mem rx union ry) conj neg (ra nmem rx conj ra mem rz)
\ &#justify(<set.difference>, iff) ra mem rx union ry conj ra nmem rz without rx
\ &#justify(<set.difference>, iff) ra mem (rx union ry) without (rz without rx)
 $
 For the second equation, we show that the #n[sets] are #n[subsets] of each other:
  + Left-to-right follows#justifyt(<set.difference.anti>) from $ry inter rz subset rz$#justifyt(<set.inter.subset>)#justifyt(<set.difference.mono>).
  + Now let $dv(a) mem (rx union ry) without ((ry inter rz) without rx)$, that is#justifyt(<set.inter.mem-iff>) #justifyt(<set.union.mem-iff>)#justifyt(<set.difference>) $ra mem rx$ or $ra mem ry$ as well as $ra nmem ry or ra nmem rz$ or $ra mem rx$.
    + If $ra mem rx$, we must have $ra nmem rz without rx$#justifyt(<set.difference>) and $ra mem rx union ry$#justifyt(<set.union.mem-iff>), hence $ra mem (rx union ry) without (rz without rx)$#justifyt(<set.difference>).
    + If $ra mem ry$, we must have $ra nmem rz$ or $ra mem rx$. In the latter case, the same applies. In the former, we have $ra mem rx union ry$#justifyt(<set.union.mem-iff>) and $ra nmem rz$ so $ra mem (rx union ry) without (rz without rx)$#justifyt(<set.difference.subset>).
+ $ dv(a) mem (rx without ry) union (rx inter ry) & #justify(<set.difference>,iff)#justifyt(<set.inter.mem-iff>)#justifyt(<set.union.mem-iff>) (ra mem rx conj ra nmem ry) disj (ra mem rx conj ra mem ry)
 \ &#justify(<and.or-distr>, iff) ra mem rx conj (ra mem ry disj ra nmem ry) \ &#justify(<excluded-middle>, iff) ra mem rx $
 and 
 $ dv(a) mem (rx without ry) inter (rx inter ry) & #justify(<set.difference>,iff)#justifyt(<set.inter.mem-iff>) (ra mem rx conj ra nmem ry) conj (ra mem rx conj ra mem ry)
 \ &#justify(<and.self>, iff) ra mem rx conj ra mem ry conj ra nmem ry \ &#justify(<and.absurd>, iff)#justifyt(<set.empty.nmem>) ra mem emptyset. $

]