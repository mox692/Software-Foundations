(** * Basics: Functional Programming in Coq *)

(* REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
*)

(* ################################################################# *)
(** * Introduction *)

(** The functional style of programming is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions as _first-class_ values --
    i.e., values that can be passed as arguments to other functions,
    returned as results, included in data structures, etc.  The
    recognition that functions can be treated as data gives rise to a
    host of useful and powerful programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and _polymorphic
    type systems_ supporting abstraction and code reuse.  Coq offers
    all of these features.

    The first half of this chapter introduces the most essential
    elements of Coq's native functional programming language, called
    _Gallina_.  The second half introduces some basic _tactics_ that
    can be used to prove properties of Gallina programs. *)

(* ################################################################# *)
(** * Data and Functions *)

(* ================================================================= *)
(** ** Enumerated Types *)

(** One notable aspect of Coq is that its set of built-in
    features is _extremely_ small.  For example, instead of providing
    the usual palette of atomic data types (booleans, integers,
    strings, etc.), Coq offers a powerful mechanism for defining new
    data types from scratch, with all these familiar types as
    instances.

    Naturally, the Coq distribution comes with an extensive standard
    library providing definitions of booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library definitions.  To
    illustrate this, in this course we will explicitly recapitulate
    (almost) all the definitions we need, rather than getting them
    from the standard library. *)

(* ================================================================= *)
(** ** Days of the Week *)

(** To see how this definition mechanism works, let's start with
    a very simple example.  The following declaration tells Coq that
    we are defining a set of data values -- a _type_. *)

    Inductive day : Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.
  
  (** The new type is called [day], and its members are [monday],
      [tuesday], etc.
  
      Having defined [day], we can write functions that operate on
      days. *)
  
  (** here is memos **)
  Definition next_weekday (d:day) : day :=
    match d with
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
    end. 
  
  (** One point to note is that the argument and return types of
      this function are explicitly declared.  Like most functional
      programming languages, Coq can often figure out these types for
      itself when they are not given explicitly -- i.e., it can do _type
      inference_ -- but we'll generally include them to make reading
      easier. *)
  
  (** Having defined a function, we should next check that it
      works on some examples.  There are actually three different ways
      to do the examples in Coq.  First, we can use the command
      [Compute] to evaluate a compound expression involving
      [next_weekday]. *)
  
  Compute (next_weekday friday).
  (* ==> monday : day *)
  
  Compute (next_weekday (next_weekday saturday)).
  (* ==> tuesday : day *)
  
  (** (We show Coq's responses in comments, but, if you have a
      computer handy, this would be an excellent moment to fire up the
      Coq interpreter under your favorite IDE -- either CoqIde or Proof
      General -- and try it for yourself.  Load this file, [Basics.v],
      from the book's Coq sources, find the above example, submit it to
      Coq, and observe the result.) *)
  
  (** Second, we can record what we _expect_ the result to be in the
      form of a Coq example: *)
  
  Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.
  
  (** This declaration does two things: it makes an
      assertion (that the second weekday after [saturday] is [tuesday]),
      and it gives the assertion a name that can be used to refer to it
      later.  Having made the assertion, we can also ask Coq to verify
      it like this: *)
  
  Proof. simpl. reflexivity.  Qed.
  
  (** The details are not important just now, but essentially this
      can be read as "The assertion we've just made can be proved by
      observing that both sides of the equality evaluate to the same
      thing."
  
      Third, we can ask Coq to _extract_, from our [Definition], a
      program in another, more conventional, programming
      language (OCaml, Scheme, or Haskell) with a high-performance
      compiler.  This facility is very interesting, since it gives us a
      path from proved-correct algorithms written in Gallina to
      efficient machine code.  (Of course, we are trusting the
      correctness of the OCaml/Haskell/Scheme compiler, and of Coq's
      extraction facility itself, but this is still a big step forward
      from the way most software is developed today.) Indeed, this is
      one of the main uses for which Coq was developed.  We'll come back
      to this topic in later chapters. *)
  
  (* ================================================================= *)
  (** ** Homework Submission Guidelines *)
  
  (** If you are using _Software Foundations_ in a course, your
      instructor may use automatic scripts to help grade your homework
      assignments.  In order for these scripts to work correctly (and
      give you that you get full credit for your work!), please be
      careful to follow these rules:
        - Do not change the names of exercises. Otherwise the grading
          scripts will be unable to find your solution.
        - Do not delete exercises.  If you skip an exercise (e.g.,
          because it is marked "optional," or because you can't solve it),
          it is OK to leave a partial proof in your [.v] file; in
          this case, please make sure it ends with [Admitted] (not, for
          example [Abort]).
        - It is fine to use additional definitions (of helper functions,
          useful lemmas, etc.) in your solutions.  You can put these
          before the theorem you are asked to prove.
        - If you introduce a helper lemma that you end up being unable
          to prove, hence end it with [Admitted], then make sure to also
          end the main theorem in which you use it with [Admitted], not
          [Qed].  That will help you get partial credit, in case you
          use that main theorem to solve a later exercise.
  
      You will also notice that each chapter (like [Basics.v]) is
      accompanied by a _test script_ ([BasicsTest.v]) that automatically
      calculates points for the finished homework problems in the
      chapter.  These scripts are mostly for the auto-grading
      tools, but you may also want to use them to double-check
      that your file is well formatted before handing it in.  In a
      terminal window, either type "[make BasicsTest.vo]" or do the
      following:
  
         coqc -Q . LF Basics.v
         coqc -Q . LF BasicsTest.v
  
      See the end of this chapter for more information about how to interpret
      the output of test scripts.
  
      There is no need to hand in [BasicsTest.v] itself (or [Preface.v]).
  
      If your class is using the Canvas system to hand in assignments...
        - If you submit multiple versions of the assignment, you may
          notice that they are given different names.  This is fine: The
          most recent submission is the one that will be graded.
        - To hand in multiple files at the same time (if more than one
          chapter is assigned in the same week), you need to make a
          single submission with all the files at once using the button
          "Add another file" just above the comment box. *)
  
  (** The [Require Export] statement on the next line tells Coq to use
      the [String] module from the standard library.  We'll use strings
      ourselves in later chapters, but we need to [Require] it here so
      that the grading scripts can use it for internal purposes. *)
  From Coq Require Export String.
  
  (* ================================================================= *)
  (** ** Booleans *)
  
  (** Following the pattern of the days of the week above, we can
      define the standard type [bool] of booleans, with members [true]
      and [false]. *)
  
  Inductive bool : Type :=
    | true
    | false.
  
  (** Functions over booleans can be defined in the same way as
      above: *)
  
  Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.
  
  Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.
  
  Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.
  
  (** (Although we are rolling our own booleans here for the sake
      of building up everything from scratch, Coq does, of course,
      provide a default implementation of the booleans, together with a
      multitude of useful functions and lemmas.  Whenever possible,
      we'll name our own definitions and theorems so that they exactly
      coincide with the ones in the standard library.) *)
  
  (** The last two of these illustrate Coq's syntax for
      multi-argument function definitions.  The corresponding
      multi-argument application syntax is illustrated by the following
      "unit tests," which constitute a complete specification -- a truth
      table -- for the [orb] function: *)
  
  Example test_orb1:  (orb true  false) = true.  
  Proof. simpl. reflexivity.  Qed.
  Example test_orb2:  (orb false false) = false.
  Proof. simpl. reflexivity.  Qed.
  Example test_orb3:  (orb false true)  = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_orb4:  (orb true  true)  = true.
  Proof. simpl. reflexivity.  Qed.
  
  (** We can also introduce some familiar infix syntax for the
      boolean operations we have just defined. The [Notation] command
      defines a new symbolic notation for an existing definition. *)
  
  Notation "x && y" := (andb x y).
  Notation "x || y" := (orb x y).
  
  Example test_orb5:  false || false || true = true.
  Proof. simpl. reflexivity. Qed.
  
  (** _A note on notation_: In [.v] files, we use square brackets
      to delimit fragments of Coq code within comments; this convention,
      also used by the [coqdoc] documentation tool, keeps them visually
      separate from the surrounding text.  In the HTML version of the
      files, these pieces of text appear in a [different font]. *)
  
  (** These examples are also an opportunity to introduce one more small
      feature of Coq's programming language: conditional expressions... *)
  
  Definition negb' (b:bool) : bool :=
    if b then false
    else true.
  
  Definition andb' (b1:bool) (b2:bool) : bool :=
    if b1 then b2
    else false.
  
  Definition orb' (b1:bool) (b2:bool) : bool :=
    if b1 then true
    else b2.
  
  (** Coq's conditionals are exactly like those found in any other
      language, with one small generalization.  Since the [bool] type is
      not built in, Coq actually supports conditional expressions over
      _any_ inductively defined type with exactly two clauses in its
      definition.  The guard is considered true if it evaluates to the
      "constructor" of the first clause of the [Inductive]
      definition (which just happens to be called [true] in this case)
      and false if it evaluates to the second. *)
  
  (** **** Exercise: 1 star, standard (nandb)
  
      The command [Admitted] can be used as a placeholder for an
      incomplete proof.  We use it in exercises to indicate the parts
      that we're leaving for you -- i.e., your job is to replace
      [Admitted]s with real proofs.
  
      Remove "[Admitted.]" and complete the definition of the following
      function; then make sure that the [Example] assertions below can
      each be verified by Coq.  (I.e., fill in each proof, following the
      model of the [orb] tests above, and make sure Coq accepts it.) The
      function should return [true] if either or both of its inputs are
      [false].
  
      Hint: if [simpl] will not simplify the goal in your proof, it's
      probably because you defined [nandb] without using a [match]
      expression. Try a different definition of [nandb], or just
      skip over [simpl] and go directly to [reflexivity]. We'll
      explain this phenomenon later in the chapter. *)
  
  Definition nandb (b1:bool) (b2:bool) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_nandb1:               (nandb true false) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb2:               (nandb false false) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb3:               (nandb false true) = true.
  (* FILL IN HERE *) Admitted.
  Example test_nandb4:               (nandb true true) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** **** Exercise: 1 star, standard (andb3)
  
      Do the same for the [andb3] function below. This function should
      return [true] when all of its inputs are [true], and [false]
      otherwise. *)
  
  Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_andb31:                 (andb3 true true true) = true.
  (* FILL IN HERE *) Admitted.
  Example test_andb32:                 (andb3 false true true) = false.
  (* FILL IN HERE *) Admitted.
  Example test_andb33:                 (andb3 true false true) = false.
  (* FILL IN HERE *) Admitted.
  Example test_andb34:                 (andb3 true true false) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (* ================================================================= *)
  (** ** Types *)
  
  (** Every expression in Coq has a type, describing what sort of
      thing it computes. The [Check] command asks Coq to print the type
      of an expression. *)
  
  Check true.
  (* ===> true : bool *)
  
  (** If the expression after [Check] is followed by a colon and a type,
      Coq will verify that the type of the expression matches the given
      type and halt with an error if not. *)
  
  Check true
    : bool.
  Check (negb true)
    : bool.
  
  (** Functions like [negb] itself are also data values, just like
      [true] and [false].  Their types are called _function types_, and
      they are written with arrows. *)
  
  Check negb
    : bool -> bool.
  
  (** The type of [negb], written [bool -> bool] and pronounced
      "[bool] arrow [bool]," can be read, "Given an input of type
      [bool], this function produces an output of type [bool]."
      Similarly, the type of [andb], written [bool -> bool -> bool], can
      be read, "Given two inputs, each of type [bool], this function
      produces an output of type [bool]." *)
  
  (* ================================================================= *)
  (** ** New Types from Old *)
  
  (** The types we have defined so far are examples of "enumerated
      types": their definitions explicitly enumerate a finite set of
      elements, called _constructors_.  Here is a more interesting type
      definition, where one of the constructors takes an argument: *)
  
  Inductive rgb : Type :=
    | red
    | green
    | blue.
  
  Inductive color : Type :=
    | black
    | white
    | primary (p : rgb).
  
  (** Let's look at this in a little more detail.
  
      An [Inductive] definition does two things:
  
      - It defines a set of new _constructors_. E.g., [red],
        [primary], [true], [false], [monday], etc. are constructors.
  
      - It groups them into a new named type, like [bool], [rgb], or
        [color].
  
      _Constructor expressions_ are formed by applying a constructor
      to zero or more other constructors or constructor expressions,
      obeying the declared number and types of the constructor arguments.
      E.g.,
          - [red]
          - [true]
          - [primary red]
          - etc.
      But not
          - [red primary]
          - [true red]
          - [primary (primary red)]
          - etc.
  *)
  
  (** In particular, the definitions of [rgb] and [color] say
      which constructor expressions belong to the sets [rgb] and
      [color]:
  
      - [red], [green], and [blue] belong to the set [rgb];
      - [black] and [white] belong to the set [color];
      - if [p] is a constructor expression belonging to the set [rgb],
        then [primary p] (pronounced "the constructor [primary] applied
        to the argument [p]") is a constructor expression belonging to
        the set [color]; and
      - constructor expressions formed in these ways are the _only_ ones
        belonging to the sets [rgb] and [color]. *)
  
  (** We can define functions on colors using pattern matching just as
      we did for [day] and [bool]. *)
  
  Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.
  
  (** Since the [primary] constructor takes an argument, a pattern
      matching [primary] should include either a variable (as above --
      note that we can choose its name freely) or a constant of
      appropriate type (as below). *)
  
  Definition isred (c : color) : bool :=
    match c with
    | black => false
    | white => false
    | primary red => true
    | primary _ => false
    end.
  
  (** The pattern "[primary _]" here is shorthand for "the constructor
      [primary] applied to any [rgb] constructor except [red]."  (The
      wildcard pattern [_] has the same effect as the dummy pattern
      variable [p] in the definition of [monochrome].) *)
  
  (* ================================================================= *)
  (** ** Modules *)
  
  (** Coq provides a _module system_ to aid in organizing large
      developments.  We won't need most of its features,
      but one is useful: If we enclose a collection of declarations
      between [Module X] and [End X] markers, then, in the remainder of
      the file after the [End], these definitions are referred to by
      names like [X.foo] instead of just [foo].  We will use this
      feature to limit the scope of definitions, so that we are free to
      reuse names. *)
  
  Module Playground.
    Definition b : rgb := blue.
  End Playground.
  
  Definition b : bool := true.
  
  Check Playground.b : rgb.
  Check b : bool.
  
  (* ================================================================= *)
  (** ** Tuples *)
  
  Module TuplePlayground.
  
  (** A single constructor with multiple parameters can be used
      to create a tuple type. As an example, consider representing
      the four bits in a nybble (half a byte). We first define
      a datatype [bit] that resembles [bool] (using the
      constructors [B0] and [B1] for the two possible bit values)
      and then define the datatype [nybble], which is essentially
      a tuple of four bits. *)
  
  Inductive bit : Type :=
    | B0
    | B1.
  
  Inductive nybble : Type :=
    | bits (b0 b1 b2 b3 : bit).
  
  Check (bits B1 B0 B1 B0)
    : nybble.
  
  (** The [bits] constructor acts as a wrapper for its contents.
      Unwrapping can be done by pattern-matching, as in the [all_zero]
      function which tests a nybble to see if all its bits are [B0].  We
      use underscore (_) as a _wildcard pattern_ to avoid inventing
      variable names that will not be used. *)
  
  Definition all_zero (nb : nybble) : bool :=
    match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
    end.
  
  Compute (all_zero (bits B1 B0 B1 B0)).
  (* ===> false : bool *)
  Compute (all_zero (bits B0 B0 B0 B0)).
  (* ===> true : bool *)
  
  End TuplePlayground.
  
  (* ================================================================= *)
  (** ** Numbers *)
  
  (** We put this section in a module so that our own definition of
      natural numbers does not interfere with the one from the
      standard library.  In the rest of the book, we'll want to use
      the standard library's. *)
  
  Module NatPlayground.
  
  (** All the types we have defined so far -- both "enumerated
      types" such as [day], [bool], and [bit] and tuple types such as
      [nybble] built from them -- are finite.  The natural numbers, on
      the other hand, are an infinite set, so we'll need to use a
      slightly richer form of type declaration to represent them.
  
      There are many representations of numbers to choose from. We are
      most familiar with decimal notation (base 10), using the digits 0
      through 9, for example, to form the number 123.  You may have
      encountered hexadecimal notation (base 16), in which the same
      number is represented as 7B, or octal (base 8), where it is 173,
      or binary (base 2), where it is 1111011. Using an enumerated type
      to represent digits, we could use any of these as our
      representation natural numbers. Indeed, there are circumstances
      where each of these choices would be useful.
  
      The binary representation is valuable in computer hardware because
      the digits can be represented with just two distinct voltage
      levels, resulting in simple circuitry. Analogously, we wish here
      to choose a representation that makes _proofs_ simpler.
  
      In fact, there is a representation of numbers that is even simpler
      than binary, namely unary (base 1), in which only a single digit
      is used (as our ancient forebears might have done to count days by
      making scratches on the walls of their caves). To represent unary
      numbers with a Coq datatype, we use two constructors. The
      capital-letter [O] constructor represents zero.  When the [S]
      constructor is applied to the representation of the natural number
      n, the result is the representation of n+1, where [S] stands for
      "successor" (or "scratch").  Here is the complete datatype
      definition. *)
  
  Inductive nat : Type :=
    | O
    | S (n : nat).
  
  (** With this definition, 0 is represented by [O], 1 by [S O],
      2 by [S (S O)], and so on. *)
  
  (** Informally, the clauses of the definition can be read:
        - [O] is a natural number (remember this is the letter "[O],"
          not the numeral "[0]").
        - [S] can be put in front of a natural number to yield another
          one -- if [n] is a natural number, then [S n] is too. *)
  
  (** Again, let's look at this in a little more detail.  The definition
      of [nat] says how expressions in the set [nat] can be built:
  
      - the constructor expression [O] belongs to the set [nat];
      - if [n] is a constructor expression belonging to the set [nat],
        then [S n] is also a constructor expression belonging to the set
        [nat]; and
      - constructor expressions formed in these two ways are the only
        ones belonging to the set [nat]. *)
  
  (** These conditions are the precise force of the [Inductive]
      declaration.  They imply that the constructor expression [O], the
      constructor expression [S O], the constructor expression [S (S
      O)], the constructor expression [S (S (S O))], and so on all
      belong to the set [nat], while other constructor expressions, like
      [true], [andb true false], [S (S false)], and [O (O (O S))] do
      not.
  
      A critical point here is that what we've done so far is just to
      define a _representation_ of numbers: a way of writing them down.
      The names [O] and [S] are arbitrary, and at this point they have
      no special meaning -- they are just two different marks that we
      can use to write down numbers (together with a rule that says any
      [nat] will be written as some string of [S] marks followed by an
      [O]).  If we like, we can write essentially the same definition
      this way: *)
  
  Inductive nat' : Type :=
    | stop
    | tick (foo : nat').
  
  (** The _interpretation_ of these marks comes from how we use them to
      compute. *)
  
  (** We can do this by writing functions that pattern match on
      representations of natural numbers just as we did above with
      booleans and days -- for example, here is the predecessor
      function: *)
  
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
  
  (** The second branch can be read: "if [n] has the form [S n']
      for some [n'], then return [n']."  *)
  
  (** The following [End] command closes the current module, so
      [nat] will refer back to the type from the standard library. *)
  
  End NatPlayground.
  
  (** Because natural numbers are such a pervasive form of data,
      Coq provides a tiny bit of built-in magic for parsing and printing
      them: ordinary decimal numerals can be used as an alternative to
      the "unary" notation defined by the constructors [S] and [O].  Coq
      prints numbers in decimal form by default: *)
  
  Check (S (S (S (S O)))).
  (* ===> 4 : nat *)
  
  Definition minustwo (n : nat) : nat :=
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.
  
  Compute (minustwo 4).
  (* ===> 2 : nat *)
  
  (** The constructor [S] has the type [nat -> nat], just like functions
      such as [pred] and [minustwo]: *)
  
  Check S        : nat -> nat.
  Check pred     : nat -> nat.
  Check minustwo : nat -> nat.
  
  (** These are all things that can be applied to a number to yield a
      number.  However, there is a fundamental difference between [S]
      and the other two: functions like [pred] and [minustwo] are
      defined by giving _computation rules_ -- e.g., the definition of
      [pred] says that [pred 2] can be simplified to [1] -- while the
      definition of [S] has no such behavior attached.  Although it is
      _like_ a function in the sense that it can be applied to an
      argument, it does not _do_ anything at all!  It is just a way of
      writing down numbers.
  
      (Think about standard decimal numerals: the numeral [1] is not a
      computation; it's a piece of data.  When we write [111] to mean
      the number one hundred and eleven, we are using [1], three times,
      to write down a concrete representation of a number.)
  
      Now let's go on and define some more functions over numbers.
  
      For most interesting computations involving numbers, simple
      pattern matching is not enough: we also need recursion.  For
      example, to check that a number [n] is even, we may need to
      recursively check whether [n-2] is even.  Such functions are
      introduced with the keyword [Fixpoint] instead of [Definition]. *)
  
  Fixpoint even (n:nat) : bool :=
    match n with
    | O        => true
    | S O      => false
    | S (S n') => even n'
    end.
  
  (** We could define [odd] by a similar [Fixpoint] declaration, but
      here is a simpler way: *)
  
  Definition odd (n:nat) : bool :=
    negb (even n).
  
  Example test_odd1:    odd 1 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_odd2:    odd 4 = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** (You may notice if you step through these proofs that
      [simpl] actually has no effect on the goal -- all of the work is
      done by [reflexivity].  We'll discuss why that is shortly.)
  
      Naturally, we can also define multi-argument functions by
      recursion.  *)
  
  Module NatPlayground2.
  
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
  
  (** Adding three to two now gives us five, as we'd expect. *)
  
  Compute (plus 3 2).
  (* ===> 5 : nat *)
  
  (** The steps of simplification that Coq performs can be
      visualized as follows: *)
  
  (*      [plus 3 2]
     i.e. [plus (S (S (S O))) (S (S O))]
      ==> [S (plus (S (S O)) (S (S O)))]
            by the second clause of the [match]
      ==> [S (S (plus (S O) (S (S O))))]
            by the second clause of the [match]
      ==> [S (S (S (plus O (S (S O)))))]
            by the second clause of the [match]
      ==> [S (S (S (S (S O))))]
            by the first clause of the [match]
     i.e. [5]  *)
  
  (** As a notational convenience, if two or more arguments have
      the same type, they can be written together.  In the following
      definition, [(n m : nat)] means just the same as if we had written
      [(n : nat) (m : nat)]. *)
  
  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.
  
  Example test_mult1: (mult 3 3) = 9.
  Proof. simpl. reflexivity.  Qed.
  
  (** You can match two expressions at once by putting a comma
      between them: *)
  
  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
    end.
  
  End NatPlayground2.
  
  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => S O
    | S p => mult base (exp base p)
    end.
  
  (** **** Exercise: 1 star, standard (factorial)
  
      Recall the standard mathematical factorial function:
  
         factorial(0)  =  1
         factorial(n)  =  n * factorial(n-1)     (if n>0)
  
      Translate this into Coq.
  
      Make sure you put a [:=] between the header we've given you and
      your definition.  If you see an error like "The reference
      factorial was not found in the current environment," it means
      you've forgotten the [:=]. *)
  
  Fixpoint factorial (n:nat) : nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Example test_factorial1:          (factorial 3) = 6.
  (* FILL IN HERE *) Admitted.
  Example test_factorial2:          (factorial 5) = (mult 10 12).
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** Again, we can make numerical expressions easier to read and write
      by introducing notations for addition, multiplication, and
      subtraction. *)
  
  Notation "x + y" := (plus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x - y" := (minus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x * y" := (mult x y)
                         (at level 40, left associativity)
                         : nat_scope.
  
  Check ((0 + 1) + 1) : nat.
  
  (** (The [level], [associativity], and [nat_scope] annotations
      control how these notations are treated by Coq's parser.  The
      details are not important for present purposes, but interested
      readers can refer to the "More on Notation" section at the end of
      this chapter.)
  
      Note that these declarations do not change the definitions we've
      already made: they are simply instructions to the Coq parser to
      accept [x + y] in place of [plus x y] and, conversely, to the Coq
      pretty-printer to display [plus x y] as [x + y]. *)
  
  (** When we say that Coq comes with almost nothing built-in, we really
      mean it: even equality testing is a user-defined operation!
      Here is a function [eqb], which tests natural numbers for
      [eq]uality, yielding a [b]oolean.  Note the use of nested
      [match]es (we could also have used a simultaneous match, as we did
      in [minus].) *)
  
  Fixpoint eqb (n m : nat) : bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => eqb n' m'
              end
    end.
  
  (** Similarly, the [leb] function tests whether its first argument is
      less than or equal to its second argument, yielding a boolean. *)
  
  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.
  
  Example test_leb1:                leb 2 2 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_leb2:                leb 2 4 = true.
  Proof. simpl. reflexivity.  Qed.
  Example test_leb3:                leb 4 2 = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** We'll be using these (especially [eqb]) a lot, so let's give
      them infix notations. *)
  
  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
  
  Example test_leb3': (4 <=? 2) = false.
  Proof. simpl. reflexivity.  Qed.
  
  (** We now have two symbols that look like equality: [=] and
      [=?].  We'll have much more to say about the differences and
      similarities between them later. For now, the main thing to notice
      is that [x = y] is a logical _claim_ -- a "proposition" -- that we
      can try to prove, while [x =? y] is an _expression_ whose
      value (either [true] or [false]) we can compute. *)
  
  (** **** Exercise: 1 star, standard (ltb)
  
      The [ltb] function tests natural numbers for [l]ess-[t]han,
      yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
      this one, define it in terms of a previously defined
      function.  (It can be done with just one previously defined
      function, but you can use two if you want.) *)
  
  Definition ltb (n m : nat) : bool
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
  
  Example test_ltb1:             (ltb 2 2) = false.
  (* FILL IN HERE *) Admitted.
  Example test_ltb2:             (ltb 2 4) = true.
  (* FILL IN HERE *) Admitted.
  Example test_ltb3:             (ltb 4 2) = false.
  (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (* ################################################################# *)
  (** * Proof by Simplification *)
  
  (** Now that we've defined a few datatypes and functions, let's
      turn to stating and proving properties of their behavior.
      Actually, we've already started doing this: each [Example] in the
      previous sections makes a precise claim about the behavior of some
      function on some particular inputs.  The proofs of these claims
      were always the same: use [simpl] to simplify both sides of the
      equation, then use [reflexivity] to check that both sides contain
      identical values.
  
      The same sort of "proof by simplification" can be used to prove
      more interesting properties as well.  For example, the fact that
      [0] is a "neutral element" for [+] on the left can be proved just
      by observing that [0 + n] reduces to [n] no matter what [n] is -- a
      fact that can be read directly off the definition of [plus]. *)
  
  Theorem plus_O_n : forall n : nat, 0 + n = n.
  Proof.
    intros n. simpl. reflexivity.  Qed.
  
  (** (You may notice that the above statement looks different in
      the [.v] file in your IDE than it does in the HTML rendition in
      your browser. In [.v] files, we write the universal quantifier
      [forall] using the reserved identifier "forall."  When the [.v]
      files are converted to HTML, this gets transformed into the
      standard upside-down-A symbol.)
  
      This is a good place to mention that [reflexivity] is a bit more
      powerful than we have acknowledged. In the examples we have seen,
      the calls to [simpl] were actually not needed, because
      [reflexivity] can perform some simplification automatically when
      checking that two sides are equal; [simpl] was just added so that
      we could see the intermediate state -- after simplification but
      before finishing the proof.  Here is a shorter proof of the
      theorem: *)
  
  Theorem plus_O_n' : forall n : nat, 0 + n = n.
  Proof.
    intros n. reflexivity. Qed.
  
  (** Moreover, it will be useful to know that [reflexivity] does
      somewhat _more_ simplification than [simpl] does -- for example,
      it tries "unfolding" defined terms, replacing them with their
      right-hand sides.  The reason for this difference is that, if
      reflexivity succeeds, the whole goal is finished and we don't need
      to look at whatever expanded expressions [reflexivity] has created
      by all this simplification and unfolding; by contrast, [simpl] is
      used in situations where we may have to read and understand the
      new goal that it creates, so we would not want it blindly
      expanding definitions and leaving the goal in a messy state.
  
      The form of the theorem we just stated and its proof are almost
      exactly the same as the simpler examples we saw earlier; there are
      just a few differences.
  
      First, we've used the keyword [Theorem] instead of [Example].
      This difference is mostly a matter of style; the keywords
      [Example] and [Theorem] (and a few others, including [Lemma],
      [Fact], and [Remark]) mean pretty much the same thing to Coq.
  
      Second, we've added the quantifier [forall n:nat], so that our
      theorem talks about _all_ natural numbers [n].  Informally, to
      prove theorems of this form, we generally start by saying "Suppose
      [n] is some number..."  Formally, this is achieved in the proof by
      [intros n], which moves [n] from the quantifier in the goal to a
      _context_ of current assumptions. Note that we could have used
      another identifier instead of [n] in the [intros] clause, (though
      of course this might be confusing to human readers of the proof): *)
  
  Theorem plus_O_n'' : forall n : nat, 0 + n = n.
  Proof.
    intros m. reflexivity. Qed.
  
  (** The keywords [intros], [simpl], and [reflexivity] are examples of
      _tactics_.  A tactic is a command that is used between [Proof] and
      [Qed] to guide the process of checking some claim we are making.
      We will see several more tactics in the rest of this chapter and
      many more in future chapters. *)
  
  (** Other similar theorems can be proved with the same pattern. *)
  
  Theorem plus_1_l : forall n:nat, 1 + n = S n.
  Proof.
    intros n. reflexivity.  Qed.
  
  Theorem mult_0_l : forall n:nat, 0 * n = 0.
  Proof.
    intros n. reflexivity.  Qed.
  
  (** The [_l] suffix in the names of these theorems is
      pronounced "on the left." *)
  
  (** It is worth stepping through these proofs to observe how the
      context and the goal change.  You may want to add calls to [simpl]
      before [reflexivity] to see the simplifications that Coq performs
      on the terms before checking that they are equal. *)
  
  (* ################################################################# *)
  (** * Proof by Rewriting *)
  
  (** The following theorem is a bit more interesting than the
      ones we've seen: *)
  
  Theorem plus_id_example : forall n m:nat,
    n = m ->
    n + n = m + m.
  
  (** Instead of making a universal claim about all numbers [n] and [m],
      it talks about a more specialized property that only holds when
      [n = m].  The arrow symbol is pronounced "implies."
  
      As before, we need to be able to reason by assuming we are given such
      numbers [n] and [m].  We also need to assume the hypothesis
      [n = m]. The [intros] tactic will serve to move all three of these
      from the goal into assumptions in the current context.
  
      Since [n] and [m] are arbitrary numbers, we can't just use
      simplification to prove this theorem.  Instead, we prove it by
      observing that, if we are assuming [n = m], then we can replace
      [n] with [m] in the goal statement and obtain an equality with the
      same expression on both sides.  The tactic that tells Coq to
      perform this replacement is called [rewrite]. *)
  
  Proof.
    (* move both quantifiers into the context: *)
    intros n m.
    (* move the hypothesis into the context: *)
    intros H.
    (* rewrite the goal using the hypothesis: *)
    rewrite -> H.
    reflexivity.  Qed.
  
  (** The first line of the proof moves the universally quantified
      variables [n] and [m] into the context.  The second moves the
      hypothesis [n = m] into the context and gives it the name [H].
      The third tells Coq to rewrite the current goal ([n + n = m + m])
      by replacing the left side of the equality hypothesis [H] with the
      right side.
  
      (The arrow symbol in the [rewrite] has nothing to do with
      implication: it tells Coq to apply the rewrite from left to right.
      In fact, you can omit the arrow, and Coq will default to rewriting
      in this direction.  To rewrite from right to left, you can use
      [rewrite <-].  Try making this change in the above proof and see
      what difference it makes.) *)
  
  (** **** Exercise: 1 star, standard (plus_id_exercise)
  
      Remove "[Admitted.]" and fill in the proof. *)
  
  Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
  Proof.
    (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** The [Admitted] command tells Coq that we want to skip trying
      to prove this theorem and just accept it as a given.  This can be
      useful for developing longer proofs, since we can state subsidiary
      lemmas that we believe will be useful for making some larger
      argument, use [Admitted] to accept them on faith for the moment,
      and continue working on the main argument until we are sure it
      makes sense; then we can go back and fill in the proofs we
      skipped.  Be careful, though: every time you say [Admitted] you
      are leaving a door open for total nonsense to enter Coq's nice,
      rigorous, formally checked world! *)
  
  (** The [Check] command can also be used to examine the statements of
      previously declared lemmas and theorems.  The two examples below
      are lemmas about multiplication that are proved in the standard
      library.  (We will see how to prove them ourselves in the next
      chapter.) *)
  
  Check mult_n_O.
  (* ===> forall n : nat, 0 = n * 0 *)
  
  Check mult_n_Sm.
  (* ===> forall n m : nat, n * m + n = n * S m *)
  
  (** We can use the [rewrite] tactic with a previously proved theorem
      instead of a hypothesis from the context. If the statement of the
      previously proved theorem involves quantified variables, as in the
      example below, Coq tries to instantiate them by matching with the
      current goal. *)
  
  Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
  Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    reflexivity. Qed.
  
  (** **** Exercise: 1 star, standard (mult_n_1)
  
      Use those two lemmas about multiplication that we just checked to
      prove the following theorem.  Hint: recall that [1] is [S O]. *)
  
  Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
  Proof.
    (* FILL IN HERE *) Admitted.
  
  (** [] *)
  
  (* ################################################################# *)
  (** * Proof by Case Analysis *)
  
  (** Of course, not everything can be proved by simple
      calculation and rewriting: In general, unknown, hypothetical
      values (arbitrary numbers, booleans, lists, etc.) can block
      simplification.  For example, if we try to prove the following
      fact using the [simpl] tactic as above, we get stuck.  (We then
      use the [Abort] command to give up on it for the moment.)*)
  
  Theorem plus_1_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros n.
    simpl.  (* does nothing! *)
  Abort.
  
  (** The reason for this is that the definitions of both [eqb]
      and [+] begin by performing a [match] on their first argument.
      But here, the first argument to [+] is the unknown number [n] and
      the argument to [eqb] is the compound expression [n + 1]; neither
      can be simplified.
  
      To make progress, we need to consider the possible forms of [n]
      separately.  If [n] is [O], then we can calculate the final result
      of [(n + 1) =? 0] and check that it is, indeed, [false].  And if
      [n = S n'] for some [n'], then, although we don't know exactly
      what number [n + 1] represents, we can calculate that, at least,
      it will begin with one [S], and this is enough to calculate that,
      again, [(n + 1) =? 0] will yield [false].
  
      The tactic that tells Coq to consider, separately, the cases where
      [n = O] and where [n = S n'] is called [destruct]. *)
  
  Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros n. destruct n as [| n'] eqn:E.
    - reflexivity.
    - reflexivity.   Qed.
  
  (** The [destruct] generates _two_ subgoals, which we must then
      prove, separately, in order to get Coq to accept the theorem.
  
      The annotation "[as [| n']]" is called an _intro pattern_.  It
      tells Coq what variable names to introduce in each subgoal.  In
      general, what goes between the square brackets is a _list of
      lists_ of names, separated by [|].  In this case, the first
      component is empty, since the [O] constructor is nullary (it
      doesn't have any arguments).  The second component gives a single
      name, [n'], since [S] is a unary constructor.
  
      In each subgoal, Coq remembers the assumption about [n] that is
      relevant for this subgoal -- either [n = 0] or [n = S n'] for some
      n'.  The [eqn:E] annotation tells [destruct] to give the name [E]
      to this equation.  Leaving off the [eqn:E] annotation causes Coq
      to elide these assumptions in the subgoals.  This slightly
      streamlines proofs where the assumptions are not explicitly used,
      but it is better practice to keep them for the sake of
      documentation, as they can help keep you oriented when working
      with the subgoals.
  
      The [-] signs on the second and third lines are called _bullets_,
      and they mark the parts of the proof that correspond to the two
      generated subgoals.  The part of the proof script that comes after
      a bullet is the entire proof for the corresponding subgoal.  In
      this example, each of the subgoals is easily proved by a single
      use of [reflexivity], which itself performs some simplification --
      e.g., the second one simplifies [(S n' + 1) =? 0] to [false] by
      first rewriting [(S n' + 1)] to [S (n' + 1)], then unfolding
      [eqb], and then simplifying the [match].
  
      Marking cases with bullets is optional: if bullets are not
      present, Coq simply asks you to prove each subgoal in sequence,
      one at a time. But it is a good idea to use bullets.  For one
      thing, they make the structure of a proof apparent, improving
      readability. Also, bullets instruct Coq to ensure that a subgoal
      is complete before trying to verify the next one, preventing
      proofs for different subgoals from getting mixed up. These issues
      become especially important in large developments, where fragile
      proofs lead to long debugging sessions.
  
      There are no hard and fast rules for how proofs should be
      formatted in Coq -- e.g., where lines should be broken and how
      sections of the proof should be indented to indicate their nested
      structure.  However, if the places where multiple subgoals are
      generated are marked with explicit bullets at the beginning of
      lines, then the proof will be readable almost no matter what
      choices are made about other aspects of layout.
  
      This is also a good place to mention one other piece of somewhat
      obvious advice about line lengths.  Beginning Coq users sometimes
      tend to the extremes, either writing each tactic on its own line
      or writing entire proofs on a single line.  Good style lies
      somewhere in the middle.  One reasonable guideline is to limit
      yourself to 80-character lines.
  
      The [destruct] tactic can be used with any inductively defined
      datatype.  For example, we use it next to prove that boolean
      negation is involutive -- i.e., that negation is its own
      inverse. *)
  
  Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
  Proof.
    intros b. destruct b eqn:E.
    - reflexivity.
    - reflexivity.  Qed.
  
  (** Note that the [destruct] here has no [as] clause because
      none of the subcases of the [destruct] need to bind any variables,
      so there is no need to specify any names.  In fact, we can omit
      the [as] clause from _any_ [destruct] and Coq will fill in
      variable names automatically.  This is generally considered bad
      style, since Coq often makes confusing choices of names when left
      to its own devices.
  
      It is sometimes useful to invoke [destruct] inside a subgoal,
      generating yet more proof obligations. In this case, we use
      different kinds of bullets to mark goals on different "levels."
      For example: *)
  
  Theorem andb_commutative : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
    - destruct c eqn:Ec.
      + reflexivity.
      + reflexivity.
  Qed.
  
  (** Each pair of calls to [reflexivity] corresponds to the
      subgoals that were generated after the execution of the [destruct c]
      line right above it. *)
  
  (** Besides [-] and [+], we can use [*] (asterisk) or any repetition
      of a bullet symbol (e.g. [--] or [***]) as a bullet.  We can also
      enclose sub-proofs in curly braces: *)
  
  Theorem andb_commutative' : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b eqn:Eb.
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. } }
    { destruct c eqn:Ec.
      { reflexivity. }
      { reflexivity. } }
  Qed.
  
  (** Since curly braces mark both the beginning and the end of a proof,
      they can be used for multiple subgoal levels, as this example
      shows. Furthermore, curly braces allow us to reuse the same bullet
      shapes at multiple levels in a proof. The choice of braces,
      bullets, or a combination of the two is purely a matter of
      taste. *)
  
  Theorem andb3_exchange :
    forall b c d, andb (andb b c) d = andb (andb b d) c.
  Proof.
    intros b c d. destruct b eqn:Eb.
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
    - destruct c eqn:Ec.
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
      { destruct d eqn:Ed.
        - reflexivity.
        - reflexivity. }
  Qed.
  
  (** **** Exercise: 2 stars, standard (andb_true_elim2)
  
      Prove the following claim, marking cases (and subcases) with
      bullets when you use [destruct].
  
      Hint: You will eventually need to destruct both Booleans, as in
      the theorems above. But, delay introducing the hypothesis until
      after you have an opportunity to simplify it.
  
      Hint 2: When you reach contradiction in the hypotheses, focus
      on how to [rewrite] with that contradiction. *)
  
  Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
  Proof.
    (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (** Before closing the chapter, let's mention one final
      convenience.  As you may have noticed, many proofs perform case
      analysis on a variable right after introducing it:
  
         intros x y. destruct y as [|y] eqn:E.
  
      This pattern is so common that Coq provides a shorthand for it: we
      can perform case analysis on a variable when introducing it by
      using an intro pattern instead of a variable name. For instance,
      here is a shorter proof of the [plus_1_neq_0] theorem
      above.  (You'll also note one downside of this shorthand: we lose
      the equation recording the assumption we are making in each
      subgoal, which we previously got from the [eqn:E] annotation.) *)
  
  Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
  Proof.
    intros [|n].
    - reflexivity.
    - reflexivity.  Qed.
  
  (** If there are no constructor arguments that need names, we can just
      write [[]] to get the case analysis. *)
  
  Theorem andb_commutative'' :
    forall b c, andb b c = andb c b.
  Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  
  (** **** Exercise: 1 star, standard (zero_nbeq_plus_1) *)
  Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
  Proof.
    (* FILL IN HERE *) Admitted.
  (** [] *)
  
  (* ================================================================= *)
  (** ** More on Notation (Optional) *)
  
  (** (In general, sections marked Optional are not needed to follow the
      rest of the book, except possibly other Optional sections.  On a
      first reading, you might want to skim these sections so that you
      know what's there for future reference.)
  
      Recall the notation definitions for infix plus and times: *)
  
  Notation "x + y" := (plus x y)
                         (at level 50, left associativity)
                         : nat_scope.
  Notation "x * y" := (mult x y)
                         (at level 40, left associativity)
                         : nat_scope.
  
  (** For each notation symbol in Coq, we can specify its _precedence
      level_ and its _associativity_.  The precedence level [n] is
      specified by writing [at level n]; this helps Coq parse compound
      expressions.  The associativity setting helps to disambiguate
      expressions containing multiple occurrences of the same
      symbol. For example, the parameters specified above for [+] and
      [*] say that the expression [1+2*3*4] is shorthand for
      [(1+((2*3)*4))]. Coq uses precedence levels from 0 to 100, and
      _left_, _right_, or _no_ associativity.  We will see more examples
      of this later, e.g., in the [Lists]
      chapter.
  
      Each notation symbol is also associated with a _notation scope_.
      Coq tries to guess what scope is meant from context, so when it
      sees [S(O*O)] it guesses [nat_scope], but when it sees the product
      type [bool*bool] (which we'll see in later chapters) it guesses
      [type_scope].  Occasionally, it is necessary to help it out with
      percent-notation by writing [(x*y)%nat], and sometimes in what Coq
      prints it will use [%nat] to indicate what scope a notation is in.
  
      Notation scopes also apply to numeral notation ([3], [4], [5], [42],
      etc.), so you may sometimes see [0%nat], which means [O] (the
      natural number [0] that we're using in this chapter), or [0%Z],
      which means the integer zero (which comes from a different part of
      the standard library).
  
      Pro tip: Coq's notation mechanism is not especially powerful.
      Don't expect too much from it. *)
  
  (* ================================================================= *)
  (** ** Fixpoints and Structural Recursion (Optional) *)
  
  (** Here is a copy of the definition of addition: *)
  
  Fixpoint plus' (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus' n' m)
    end.
  
  (** When Coq checks this definition, it notes that [plus'] is
      "decreasing on 1st argument."  What this means is that we are
      performing a _structural recursion_ over the argument [n] -- i.e.,
      that we make recursive calls only on strictly smaller values of
      [n].  This implies that all calls to [plus'] will eventually
      terminate.  Coq demands that some argument of _every_ [Fixpoint]
      definition is "decreasing."
  
      This requirement is a fundamental feature of Coq's design: In
      particular, it guarantees that every function that can be defined
      in Coq will terminate on all inputs.  However, because Coq's
      "decreasing analysis" is not very sophisticated, it is sometimes
      necessary to write functions in slightly unnatural ways. *)
  
  (** **** Exercise: 2 stars, standard, optional (decreasing)
  
      To get a concrete sense of this, find a way to write a sensible
      [Fixpoint] definition (of a simple function on numbers, say) that
      _does_ terminate on all inputs, but that Coq will reject because
      of this restriction.  (If you choose to turn in this optional
      exercise as part of a homework assignment, make sure you comment
      out your solution so that it doesn't cause Coq to reject the whole
      file!) *)
  
  (* FILL IN HERE
  
      [] *)
  
  (* ################################################################# *)
  (** * More Exercises *)
  
  (** **** Exercise: 1 star, standard (identity_fn_applied_twice)
  
      Use the tactics you have learned so far to prove the following
      theorem about boolean functions. *)
  
  Theorem identity_fn_applied_twice :
    forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
  Proof.
    (* FILL IN HERE *) Admitted.
  
  (** [] *)
  
  (** **** Exercise: 1 star, standard (negation_fn_applied_twice)
  
      Now state and prove a theorem [negation_fn_applied_twice] similar
      to the previous one but where the second hypothesis says that the
      function [f] has the property that [f x = negb x]. *)
  
  (* FILL IN HERE *)
  
  (* Do not modify the following line: *)
  Definition manual_grade_for_negation_fn_applied_twice : option (nat*string) := None.
  (** (The last definition is used by the autograder.)
  
      [] *)
  
  (** **** Exercise: 3 stars, standard, optional (andb_eq_orb)
  
      Prove the following theorem.  (Hint: This one can be a bit tricky,
      depending on how you approach it.  You will probably need both
      [destruct] and [rewrite], but destructing everything in sight is
      not the best way.) *)
  
  Theorem andb_eq_orb :
    forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
  Proof.
    (* FILL IN HERE *) Admitted.
  
  (** [] *)
  
  (** **** Exercise: 3 stars, standard (binary)
  
      We can generalize our unary representation of natural numbers to
      the more efficient binary representation by treating a binary
      number as a sequence of constructors [B0] and [B1] (representing 0s
      and 1s), terminated by a [Z]. For comparison, in the unary
      representation, a number is a sequence of [S] constructors terminated
      by an [O].
  
      For example:
  
          decimal               binary                          unary
             0                       Z                              O
             1                    B1 Z                            S O
             2                B0 (B1 Z)                        S (S O)
             3                B1 (B1 Z)                     S (S (S O))
             4            B0 (B0 (B1 Z))                 S (S (S (S O)))
             5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
             6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
             7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
             8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))
  
      Note that the low-order bit is on the left and the high-order bit
      is on the right -- the opposite of the way binary numbers are
      usually written.  This choice makes them easier to manipulate. *)
  
  Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).
  
  (** Complete the definitions below of an increment function [incr]
      for binary numbers, and a function [bin_to_nat] to convert
      binary numbers to unary numbers. *)
  
  Fixpoint incr (m:bin) : bin
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  Fixpoint bin_to_nat (m:bin) : nat
    (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
  
  (** The following "unit tests" of your increment and binary-to-unary
      functions should pass after you have defined those functions correctly.
      Of course, unit tests don't fully demonstrate the correctness of
      your functions!  We'll return to that thought at the end of the
      next chapter. *)
  
  Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
  (* FILL IN HERE *) Admitted.
  
  Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
  (* FILL IN HERE *) Admitted.
  
  Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
  (* FILL IN HERE *) Admitted.
  
  Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
  (* FILL IN HERE *) Admitted.
  
  Example test_bin_incr5 :
          bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
  (* FILL IN HERE *) Admitted.
  
  Example test_bin_incr6 :
          bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
  (* FILL IN HERE *) Admitted.
  
  (** [] *)
  
  (* ################################################################# *)
  (** * Testing Your Solutions *)
  
  (** Each SF chapter comes with a test file containing scripts that
      check whether you have solved the required exercises. If you're
      using SF as part of a course, your instructors will likely be
      running these test files to autograde your solutions. You can also
      use these test files, if you like, to make sure you haven't missed
      anything.
  
      Important: This step is _optional_: if you've completed all the
      non-optional exercises and Coq accepts your answers, this already
      shows that you are in good shape.
  
      The test file for this chapter is [BasicsTest.v]. To run it, make
      sure you have saved [Basics.v] to disk.  Then do this:
  
         coqc -Q . LF Basics.v
         coqc -Q . LF BasicsTest.v
  
      (Make sure you do this in a directory that also contains a file named
      [_CoqProject] containing the single line [-Q . LF].)
  
      If you accidentally deleted an exercise or changed its name, then
      [make BasicsTest.vo] will fail with an error that tells you the
      name of the missing exercise.  Otherwise, you will get a lot of
      useful output:
  
      - First will be all the output produced by [Basics.v] itself.  At
        the end of that you will see [COQC BasicsTest.v].
  
      - Second, for each required exercise, there is a report that tells
        you its point value (the number of stars or some fraction
        thereof if there are multiple parts to the exercise), whether
        its type is ok, and what assumptions it relies upon.
  
        If the _type_ is not [ok], it means you proved the wrong thing:
        most likely, you accidentally modified the theorem statement
        while you were proving it.  The autograder won't give you any
        points for that, so make sure to correct the theorem.
  
        The _assumptions_ are any unproved theorems which your solution
        relies upon.  "Closed under the global context" is a fancy way
        of saying "none": you have solved the exercise. (Hooray!)  On
        the other hand, a list of axioms means you haven't fully solved
        the exercise. (But see below regarding "Allowed Axioms.") If the
        exercise name itself is in the list, that means you haven't
        solved it; probably you have [Admitted] it.
  
      - Third, you will see the maximum number of points in standard and
        advanced versions of the assignment.  That number is based on
        the number of stars in the non-optional exercises.
  
      - Fourth, you will see a list of "Allowed Axioms".  These are
        unproved theorems that your solution is permitted to depend
        upon.  You'll probably see something about
        [functional_extensionality] for this chapter; we'll cover what
        that means in a later chapter.
  
      - Finally, you will see a summary of whether you have solved each
        exercise.  Note that summary does not include the critical
        information of whether the type is ok (that is, whether you
        accidentally changed the theorem statement): you have to look
        above for that information.
  
      Exercises that are manually graded will also show up in the
      output.  But since they have to be graded by a human, the test
      script won't be able to tell you much about them.  *)
  
  (* 2022-08-08 17:13 *)
  (** * Induction: Proof by Induction *)

(* ################################################################# *)
(** * Separate Compilation *)

(** Before getting started on this chapter, we need to import
    all of our definitions from the previous chapter: *)

(** For this [Require Export] command to work, Coq needs to be
    able to find a compiled version of [Basics.v], called [Basics.vo],
    in a directory associated with the prefix [LF].  This file is
    analogous to the [.class] files compiled from [.java] source files
    and the [.o] files compiled from [.c] files.

    First create a file named [_CoqProject] containing the following
    line (if you obtained the whole volume "Logical Foundations" as a
    single archive, a [_CoqProject] should already exist and you can
    skip this step):

      -Q . LF

    This maps the current directory ("[.]", which contains [Basics.v],
    [Induction.v], etc.) to the prefix (or "logical directory")
    "[LF]".  Proof General and CoqIDE read [_CoqProject]
    automatically, so they know to where to look for the file
    [Basics.vo] corresponding to the library [LF.Basics].

    Once [_CoqProject] is thus created, there are various ways to
    build [Basics.vo]:

     - In Proof General or CoqIDE, the compilation should happen
       automatically when you submit the [Require] line above to PG.

     - If you want to compile from the command line, generate a
       [Makefile] using the [coq_makefile] utility, which comes
       installed with Coq (if you obtained the whole volume as a
       single archive, a [Makefile] should already exist and you can
       skip this step):

         coq_makefile -f _CoqProject *.v -o Makefile

       Note: You should rerun that command whenever you add or remove
       Coq files to the directory.

       Now you can compile [Basics.v] by running [make] with the
       corresponding [.vo] file as a target:

         make Basics.vo

       All files in the directory can be compiled by giving no
       arguments:

         make

       Under the hood, [make] uses the Coq compiler, [coqc].  You can
       also run [coqc] directly:

         coqc -Q . LF Basics.v

       But [make] also calculates dependencies between source files to
       compile them in the right order, so [make] should generally be
       preferred over explicit [coqc].

    If you have trouble (e.g., if you get complaints about missing
    identifiers later in the file), it may be because the "load path"
    for Coq is not set up correctly.  The [Print LoadPath.] command
    may be helpful in sorting out such issues.

    In particular, if you see a message like

        Compiled library Foo makes inconsistent assumptions over
        library Bar

    check whether you have multiple installations of Coq on your
    machine.  It may be that commands (like [coqc]) that you execute
    in a terminal window are getting a different version of Coq than
    commands executed by Proof General or CoqIDE.

    - Another common reason is that the library [Bar] was modified and
      recompiled without also recompiling [Foo] which depends on it.
      Recompile [Foo], or everything if too many files are
      affected.  (Using the third solution above: [make clean; make].)

    One more tip for CoqIDE users: If you see messages like [Error:
    Unable to locate library Basics], a likely reason is
    inconsistencies between compiling things _within CoqIDE_ vs _using
    [coqc] from the command line_.  This typically happens when there
    are two incompatible versions of [coqc] installed on your
    system (one associated with CoqIDE, and one associated with [coqc]
    from the terminal).  The workaround for this situation is
    compiling using CoqIDE only (i.e. choosing "make" from the menu),
    and avoiding using [coqc] directly at all. *)

(* ################################################################# *)
(** * Proof by Induction *)

(** We can prove that [0] is a neutral element for [+] on the _left_
    using just [reflexivity].  But the proof that it is also a neutral
    element on the _right_ ... *)

Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... can't be done in the same simple way.  Just applying
  [reflexivity] doesn't work, since the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** And reasoning by cases using [destruct n] doesn't get us much
    further: the branch of the case analysis where we assume [n = 0]
    goes through fine, but in the branch where [n = S n'] for some [n'] we
    get stuck in exactly the same way. *)

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** We could use [destruct n'] to get one step further, but,
    since [n] can be arbitrarily large, we'll never get all the there
    if we just go on like this. *)

(** To prove interesting facts about numbers, lists, and other
    inductively defined sets, we often need a more powerful reasoning
    principle: _induction_.

    Recall (from high school, a discrete math course, etc.) the
    _principle of induction over natural numbers_: If [P(n)] is some
    proposition involving a natural number [n] and we want to show
    that [P] holds for all numbers [n], we can reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same: we begin with the goal of proving
    [P(n)] for all [n] and break it down (by applying the [induction]
    tactic) into two separate subgoals: one where we must show [P(O)]
    and another where we must show [P(n') -> P(S n')].  Here's how
    this works for the theorem at hand: *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  Since there are two subgoals, the [as...] clause
    has two parts, separated by [|].  (Strictly speaking, we can omit
    the [as...] clause and Coq will choose names for us.  In practice,
    this is a bad idea, as Coq's automatic choices tend to be
    confusing.)

    In the first subgoal, [n] is replaced by [0].  No new variables
    are introduced (so the first part of the [as...] is empty), and
    the goal becomes [0 = 0 + 0], which follows by simplification.

    In the second subgoal, [n] is replaced by [S n'], and the
    assumption [n' + 0 = n'] is added to the context with the name
    [IHn'] (i.e., the Induction Hypothesis for [n']).  These two names
    are specified in the second part of the [as...] clause.  The goal
    in this case becomes [S n' = (S n') + 0], which simplifies to
    [S n' = S (n' + 0)], which in turn follows from [IHn']. *)

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** (The use of the [intros] tactic in these proofs is actually
    redundant.  When applied to a goal that contains quantified
    variables, the [induction] tactic will automatically move them
    into the context as needed.) *)

(** **** Exercise: 2 stars, standard, especially useful (basic_induction)

    Prove the following using induction. You might need previously
    proven results. *)

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (double_plus)

    Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (eqb_refl)

    The following theorem relates the computational equality [=?] on
    [nat] with the definitional equality [=] on [bool]. *)
Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (even_S)

    One inconvenient aspect of our definition of [even n] is the
    recursive call on [n - 2]. This makes proofs about [even n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [even (S n)] that works better
    with induction: *)

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (destruct_induction)

    Briefly explain the difference between the tactics [destruct]
    and [induction].

(* FILL IN HERE *)
*)

(** [] *)

(* ################################################################# *)
(** * Proofs Within Proofs *)

(** In Coq, as in informal mathematics, large proofs are often
    broken into a sequence of theorems, with later proofs referring to
    earlier theorems.  But sometimes a proof will involve some
    miscellaneous fact that is too trivial and of too little general
    interest to bother giving it its own top-level name.  In such
    cases, it is convenient to be able to simply state and prove the
    needed "sub-theorem" right at the point where it is used.  The
    [assert] tactic allows us to do this. *)

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.

(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (We can also name the assertion with [as] just as
    we did above with [destruct] and [induction], i.e., [assert (n + 0
    + 0 = n) as H].)  Note that we surround the proof of this
    assertion with curly braces [{ ... }], both for readability and so
    that, when using Coq interactively, we can see more easily when we
    have finished this sub-proof.  The second goal is the same as the
    one at the point where we invoke [assert] except that, in the
    context, we now have the assumption [H] that [n + 0 + 0 = n].
    That is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** As another example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to use
    the commutativity of addition ([add_comm]) to rewrite one into the
    other.  However, the [rewrite] tactic is not very smart about
    _where_ it applies the rewrite.  There are three uses of [+] here,
    and it turns out that doing [rewrite -> add_comm] will affect only
    the _outer_ one... *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like add_comm should do the trick! *)
  rewrite add_comm.
  (* Doesn't work... Coq rewrites the wrong plus! :-( *)
Abort.

(** To use [add_comm] at the point where we need it, we can introduce
    a local lemma stating that [n + m = m + n] (for the _particular_ [m]
    and [n] that we are talking about here), prove this lemma using
    [add_comm], and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.

(* ################################################################# *)
(** * Formal vs. Informal Proof *)

(** "_Informal proofs are algorithms; formal proofs are code_." *)

(** What constitutes a successful proof of a mathematical claim?
    The question has challenged philosophers for millennia, but a
    rough and ready definition could be this: A proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true --
    an unassailable argument for the truth of [P].  That is, a proof
    is an act of communication.

    Acts of communication may involve different sorts of readers.  On
    one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is that [P] can be mechanically
    derived from a certain set of formal logical rules, and the proof
    is a recipe that guides the program in checking this fact.  Such
    recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    and will thus necessarily be _informal_.  Here, the criteria for
    success are less clearly specified.  A "valid" proof is one that
    makes the reader believe [P].  But the same proof may be read by
    many different readers, some of whom may be convinced by a
    particular way of phrasing the argument, while others may not be.
    Some readers may be particularly pedantic, inexperienced, or just
    plain thick-headed; the only way to convince them will be to make
    the argument in painstaking detail.  But other readers, more
    familiar in the area, may find all this detail so overwhelming
    that they lose the overall thread; all they want is to be told the
    main ideas, since it is easier for them to fill in the details for
    themselves than to wade through a written presentation of them.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.

    In practice, however, mathematicians have developed a rich set of
    conventions and idioms for writing about complex mathematical
    objects that -- at least within a certain community -- make
    communication fairly reliable.  The conventions of this stylized
    form of communication give a fairly clear standard for judging
    proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can
    completely forget about informal ones!  Formal proofs are useful
    in many ways, but they are _not_ very efficient ways of
    communicating ideas between human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this.  For a human, however, it
    is difficult to make much sense of it.  We can use comments and
    bullets to show the structure a little more clearly... *)

Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - (* n = 0 *)
    reflexivity.
  - (* n = S n' *)
    simpl. rewrite IHn'. reflexivity.   Qed.

(** ... and if you're used to Coq you might be able to step
    through the tactics one after the other in your mind and imagine
    the state of the context and goal stack at each point, but if the
    proof were even a little bit more complicated this would be next
    to impossible.

    A (pedantic) mathematician might write the proof something like
    this: *)

(** - _Theorem_: For any [n], [m] and [p],

      n + (m + p) = (n + m) + p.

    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show that

        0 + (m + p) = (0 + m) + p.

      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where

        n' + (m + p) = (n' + m) + p.

      We must now show that

        (S n') + (m + p) = ((S n') + m) + p.

      By the definition of [+], this follows from

        S (n' + (m + p)) = S ((n' + m) + p),

      which is immediate from the induction hypothesis.  _Qed_. *)

(** The overall form of the proof is basically similar, and of
    course this is no accident: Coq has been designed so that its
    [induction] tactic generates the same sub-goals, in the same
    order, as the bullet points that a mathematician would write.  But
    there are significant differences of detail: the formal proof is
    much more explicit in some ways (e.g., the use of [reflexivity])
    but much less explicit in others (in particular, the "proof state"
    at any given point in the Coq proof is completely implicit,
    whereas the informal proof reminds the reader several times where
    things stand). *)

(** **** Exercise: 2 stars, advanced, especially useful (add_comm_informal)

    Translate your solution for [add_comm] into an informal proof:

    Theorem: Addition is commutative.

    Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_comm_informal : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (eqb_refl_informal)

    Write an informal proof of the following theorem, using the
    informal proof of [add_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!

    Theorem: [(n =? n) = true] for any [n].

    Proof: (* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * More Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (mul_comm)

    Use [assert] to help prove [add_shuffle3].  You don't need to
    use induction yet. *)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now prove commutativity of multiplication.  You will probably want
    to look for (or define and prove) a "helper" theorem to be used in
    the proof of this one. Hint: what is [n * (1 + k)]? *)

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (plus_leb_compat_l)

    If a hypothesis has the form [H: P -> a = b], then [rewrite H] will
    rewrite [a] to [b] in the goal, and add [P] as a new subgoal. Use
    that in the inductive step of this exercise. *)

Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_exercises)

    Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before you hack!) *)

Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (add_shuffle3')

    The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to: [replace (t) with (u)]
   replaces (all copies of) expression [t] in the goal by expression
   [u], and generates [t = u] as an additional subgoal. This is often
   useful when a plain [rewrite] acts on the wrong part of the goal.

   Use the [replace] tactic to do a proof of [add_shuffle3'], just like
   [add_shuffle3] but without needing [assert]. *)

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Nat to Bin and Back to Nat *)

(** Recall the [bin] type we defined in [Basics]: *)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.
(** Before you start working on the next exercise, replace the stub
    definitions of [incr] and [bin_to_nat], below, with your solution
    from [Basics].  That will make it possible for this file to
    be graded on its own. *)

Fixpoint incr (m:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Fixpoint bin_to_nat (m:bin) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** In [Basics], we did some unit testing of [bin_to_nat], but we
    didn't prove its correctness. Now we'll do so. *)

(** **** Exercise: 3 stars, standard, especially useful (binary_commute)

    Prove that the following diagram commutes:

                            incr
              bin ----------------------> bin
               |                           |
    bin_to_nat |                           |  bin_to_nat
               |                           |
               v                           v
              nat ----------------------> nat
                             S

    That is, incrementing a binary number and then converting it to
    a (unary) natural number yields the same result as first converting
    it to a natural number and then incrementing.

    If you want to change your previous definitions of [incr] or [bin_to_nat]
    to make the property easier to prove, feel free to do so! *)

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (nat_bin_nat) *)

(** Write a function to convert natural numbers to binary numbers. *)

Fixpoint nat_to_bin (n:nat) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Prove that, if we start with any [nat], convert it to [bin], and
    convert it back, we get the same [nat] which we started with.

    Hint: This proof should go through smoothly using the previous
    exercise about [incr] as a lemma. If not, revisit your definitions
    of the functions involved and consider whether they are more
    complicated than necessary: the shape of a proof by induction will
    match the recursive structure of the program being verified, so
    make the recursions as simple as possible. *)

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* ################################################################# *)
(** * Bin to Nat and Back to Bin (Advanced) *)

(** The opposite direction -- starting with a [bin], converting to [nat],
    then converting back to [bin] -- turns out to be problematic. That
    is, the following theorem does not hold. *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** Let's explore why that theorem fails, and how to prove a modified
    version of it. We'll start with some lemmas that might seem
    unrelated, but will turn out to be relevant. *)

(** **** Exercise: 2 stars, advanced (double_bin) *)

(** Prove this lemma about [double], which we defined earlier in the
    chapter. *)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  (* FILL IN HERE *) Admitted.

(** Now define a similar doubling function for [bin]. *)

Definition double_bin (b:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** Check that your function correctly doubles zero. *)

Example double_bin_zero : double_bin Z = Z.
(* FILL IN HERE *) Admitted.

(** Prove this lemma, which corresponds to [double_incr]. *)

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** Let's return to our desired theorem: *)

Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.
Abort.

(** The theorem fails because there are some [bin] such that we won't
    necessarily get back to the _original_ [bin], but instead to an
    "equivalent" [bin].  (We deliberately leave that notion undefined
    here for you to think about.)

    Explain in a comment, below, why this failure occurs. Your
    explanation will not be graded, but it's important that you get it
    clear in your mind before going on to the next part. If you're
    stuck on this, think about alternative implementations of
    [double_bin] that might have failed to satisfy [double_bin_zero]
    yet otherwise seem correct. *)

(* FILL IN HERE *)

(** To solve that problem, we can introduce a _normalization_ function
    that selects the simplest [bin] out of all the equivalent
    [bin]. Then we can prove that the conversion from [bin] to [nat] and
    back again produces that normalized, simplest [bin]. *)

(** **** Exercise: 4 stars, advanced (bin_nat_bin) *)

(** Define [normalize]. You will need to keep its definition as simple
    as possible for later proofs to go smoothly. Do not use
    [bin_to_nat] or [nat_to_bin], but do use [double_bin].

    Hint: Structure the recursion such that it _always_ reaches the
    end of the [bin] and process each bit only once. Do not try to
    "look ahead" at future bits. *)

Fixpoint normalize (b:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** It would be wise to do some [Example] proofs to check that your definition of
    [normalize] works the way you intend before you proceed. They won't be graded,
    but fill them in below. *)

(* FILL IN HERE *)

(** Finally, prove the main theorem. The inductive cases could be a
    bit tricky.

    Hint 1: Start by trying to prove the main statement, see where you
    get stuck, and see if you can find a lemma -- perhaps requiring
    its own inductive proof -- that will allow the main proof to make
    progress. You might end up with a couple of these.

    Hint 2: Lemma [double_incr_bin] that you proved above will be
    helpful, too.*)

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(* 2022-08-08 17:13 *)

(** * Lists: Working with Structured Data *)


(* ################################################################# *)
(** * Pairs of Numbers *)

(** In an [Inductive] type definition, each constructor can take
    any number of arguments -- none (as with [true] and [O]), one (as
    with [S]), or more than one (as with [nybble], and here): *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(** This declaration can be read: "The one and only way to
    construct a pair of numbers is by applying the constructor [pair]
    to two arguments of type [nat]." *)

Check (pair 3 5) : natprod.

(** Functions for extracting the first and second components of a pair
    can then be defined by pattern matching. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Since pairs will be used heavily in what follows, it is nice
    to be able to write them with the standard mathematical notation
    [(x,y)] instead of [pair x y].  We can tell Coq to allow this with
    a [Notation] declaration. *)

Notation "( x , y )" := (pair x y).

(** The new notation can be used both in expressions and in pattern
    matches. *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Note that pattern-matching on a pair (with parentheses: [(x, y)])
    is not to be confused with the "multiple pattern" syntax (with no
    parentheses: [x, y]) that we have seen previously.  The above
    examples illustrate pattern matching on a pair with elements [x]
    and [y], whereas, for example, the definition of [minus] in
    [Basics] performs pattern matching on the values [n] and [m]:

       Fixpoint minus (n m : nat) : nat :=
         match n, m with
         | O   , _    => O
         | S _ , O    => n
         | S n', S m' => minus n' m'
         end.

    The distinction is minor, but it is worth knowing that they
    are not the same. For instance, the following definitions are
    ill-formed:

        (* Can't match on a pair with multiple patterns: *)
        Definition bad_fst (p : natprod) : nat :=
          match p with
          | x, y => x
          end.

        (* Can't match on multiple values with pair patterns: *)
        Definition bad_minus (n m : nat) : nat :=
          match n, m with
          | (O   , _   ) => O
          | (S _ , O   ) => n
          | (S n', S m') => bad_minus n' m'
          end.
*)

(** Now let's try to prove a few simple facts about pairs.

    If we state properties of pairs in a slightly peculiar way, we can
    sometimes complete their proofs with just reflexivity (and its
    built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.

(** But just [reflexivity] is not enough if we state the lemma in the
    most natural way: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

(** Instead, we need to expose the structure of [p] so that
    [simpl] can perform the pattern match in [fst] and [snd].  We can
    do this with [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(** Notice that, unlike its behavior with [nat]s, where it
    generates two subgoals, [destruct] generates just one subgoal
    here.  That's because [natprod]s can only be constructed in one
    way. *)

(** **** Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Lists of Numbers *)

(** Generalizing the definition of pairs, we can describe the
    type of _lists_ of numbers like this: "A list is either the empty
    list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(** For example, here is a three-element list: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** It is not necessary to understand the details of these
    declarations, but here is roughly what's going on in case you are
    interested.  The "[right associativity]" annotation tells Coq how to
    parenthesize expressions involving multiple uses of [::] so that,
    for example, the next three declarations mean exactly the same
    thing: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** The "[at level 60]" part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    the [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
    will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than
    [1 + (2 :: [3])].

    (Expressions like "[1 + 2 :: [3]]" can be a little confusing when
    you read them in a [.v] file.  The inner brackets, around 3, indicate
    a list, but the outer brackets, which are invisible in the HTML
    rendering, are there to instruct the "coqdoc" tool that the bracketed
    part should be displayed as Coq code rather than running text.)

    The second and third [Notation] declarations above introduce the
    standard square-bracket notation for lists; the right-hand side of
    the third one illustrates Coq's syntax for declaring n-ary
    notations and translating them to nested sequences of binary
    constructors. *)

(* ----------------------------------------------------------------- *)
(** *** Repeat *)

(** Next let's look at several functions for constructing and
    manipulating lists.  First, the [repeat] function takes a number
    [n] and a [count] and returns a list of length [count] in which
    every element is [n]. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Length *)

(** The [length] function calculates the length of a list. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Append *)

(** The [app] function concatenates (appends) two lists. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** Since [app] will be used extensively, it is again convenient
    to have an infix operator for it. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Head and Tail *)

(** Here are two smaller examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tl] returns everything but the first element (the
    "tail").  Since the empty list has no first element, we pass
    a default value to be returned in that case.  *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** Exercises *)

(** **** Exercise: 2 stars, standard, especially useful (list_funs)

    Complete the definitions of [nonzeros], [oddmembers], and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

Fixpoint nonzeros (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* FILL IN HERE *) Admitted.

(** For [countoddmembers], we're giving you a header that uses keyword
    [Definition] instead of [Fixpoint].  The point of stating the
    question this way is to encourage you to implement the function by
    using already-defined functions, rather than writing your own
    recursive definition. *)

Definition countoddmembers (l:natlist) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* FILL IN HERE *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced (alternate)

    Complete the following definition of [alternate], which
    interleaves two lists into one, alternating between elements taken
    from the first list and elements from the second.  See the tests
    below for more specific examples.

    Hint: there is an elegant way of writing [alternate] that fails to
    satisfy Coq's requirement that all [Fixpoint] definitions be
    _structurally recursing_, as mentioned in [Basics]. If you
    encounter that difficulty, consider pattern matching against both
    lists at the same time with the "multiple pattern" syntax we've
    seen before. *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* FILL IN HERE *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* FILL IN HERE *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    representation for a bag of numbers is as a list. *)

Definition bag := natlist.

(** **** Exercise: 3 stars, standard, especially useful (bag_functions)

    Complete the following definitions for the functions [count],
    [sum], [add], and [member] for bags. *)

Fixpoint count (v : nat) (s : bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** All these proofs can be done just by [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* FILL IN HERE *) Admitted.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't call this operation [union].)

    We've deliberately given you a header that does not give explicit
    names to the arguments.  Implement [sum] with an already-defined
    function without changing the header. *)

Definition sum : bag -> bag -> bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v : nat) (s : bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint member (v : nat) (s : bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* FILL IN HERE *) Admitted.

Example test_member2:             member 2 [1;4;1] = false.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bag_more_functions)

    Here are some more [bag] functions for you to practice with. *)

(** When [remove_one] is applied to a bag without the number to
    remove, it should return the same bag unchanged.  (This exercise
    is optional, but students following the advanced track will need
    to fill in the definition of [remove_one] for a later
    exercise.) *)

Fixpoint remove_one (v : nat) (s : bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* FILL IN HERE *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* FILL IN HERE *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint included (s1 : bag) (s2 : bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_included1:              included [1;2] [2;1;4;1] = true.
 (* FILL IN HERE *) Admitted.
Example test_included2:              included [1;2;2] [2;1;4;1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (add_inc_count)

    Adding a value to a bag should increase the value's count by one.
    State this as a theorem and prove it. *)
(*
Theorem add_inc_count : ...
Proof.
  ...
Qed.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_add_inc_count : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, just the simplification performed by [reflexivity] is
    enough for this theorem... *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ...because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs.  We'll see how to do this next. *)

(** (Micro-Sermon: As we get deeper into this material, simply
    _reading_ proof scripts will not get you very far!  It is
    important to step through the details of each one using Coq and
    think about what each step achieves.  Otherwise it is more or less
    guaranteed that the exercises will make no sense when you get to
    them.  'Nuff said.) *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors.  For example, a boolean can be either [true] or
    [false]; a number can be either [O] or [S] applied to another
    number; and a list can be either [nil] or [cons] applied to a
    number and a list.   Moreover, applications of the declared
    constructors to one another are the _only_ possible shapes
    that elements of an inductively defined set can have.

    This last fact directly gives rise to a way of reasoning about
    inductively defined sets: a number is either [O] or else it is [S]
    applied to some _smaller_ number; a list is either [nil] or else
    it is [cons] applied to some number and some _smaller_ list;
    etc. So, if we have in mind some proposition [P] that mentions a
    list [l] and we want to argue that [P] holds for _all_ lists, we
    can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can always be broken down into smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case.

    Once again, this Coq proof is not especially illuminating as a
    static document -- it is easy to see what's going on if you are
    reading the proof in an interactive Coq session and you can see
    the current goal and context at each point, but this state is not
    visible in the written-down parts of the Coq proof.  So a
    natural-language proof -- one written for human readers -- will
    need to include more explicit signposts; in particular, it will
    help the reader stay oriented if we remind them exactly what the
    induction hypothesis is in the second case. *)

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
               [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing
    function [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** For something a bit more challenging than the proofs
    we've seen so far, let's prove that reversing a list does not
    change its length.  Our first attempt gets stuck in the successor
    case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress at the point where we got
    stuck and state it as a separate lemma. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

(** For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show

        length ([] ++ l2) = length [] + length l2,

      which follows directly from the definitions of
      [length], [++], and [plus].

    - Next, suppose [l1 = n::l1'], with

        length (l1' ++ l2) = length l1' + length l2.

      We must show

        length ((n::l1') ++ l2) = length (n::l1') + length l2.

      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show

          length (rev []) = length [],

        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with

          length (rev l') = length l'.

        We must show

          length (rev (n :: l')) = length (n :: l').

        By the definition of [rev], this follows from

          length ((rev l') ++ [n]) = S (length l')

        which, by the previous lemma, is the same as

          length (rev l') + length [n] = S (length l').

        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)

(** The style of these proofs is rather longwinded and pedantic.
    After reading a couple like this, we might find it easier to
    follow proofs that give fewer details (which we can easily work
    out in our own minds or on scratch paper if necessary) and just
    highlight the non-obvious steps.  In this more compressed style,
    the above proof might look like this: *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l], by a straightforward induction on [l].  The main
     property again follows by induction on [l], using the observation
     together with the induction hypothesis in the case where [l =
     n'::l']. [] *)

(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that they will already be familiar with.
    The more pedantic style is a good default for our present
    purposes. *)

(* ================================================================= *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Let's say
    you've forgotten the name of a theorem about [rev].  The command
    [Search rev] will cause Coq to display a list of all theorems
    involving [rev]. *)

Search rev.

(** Or say you've forgotten the name of the theorem showing that plus
    is commutative.  You can use a pattern to search for all theorems
    involving the equality of two additions. *)

Search (_ + _ = _ + _).

(** You'll see a lot of results there, nearly all of them from the
    standard library.  To restrict the results, you can search inside
    a particular module: *)

Search (_ + _ = _ + _) inside Induction.

(** You can also make the search more precise by using variables in
    the search pattern instead of wildcards: *)

Search (?x + ?y = ?y + ?x).

(** The question mark in front of the variable is needed to indicate
    that it is a variable in the search pattern, rather than a
    variable that is expected to be in scope currently. *)

(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    Your IDE likely has its own functionality to help with searching.
    For example, in ProofGeneral, you can run [Search] with [C-c C-a
    C-a], and paste its response into your buffer with [C-c C-;]. *)

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Exercise: 3 stars, standard (list_exercises)

    More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* FILL IN HERE *) Admitted.

(** An _involution_ is a function that is its own inverse. That is,
    applying the function twice yield the original input. *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (eqblist)

    Fill in the definition of [eqblist], which compares
    lists of numbers for equality.  Prove that [eqblist l l]
    yields [true] for every list [l]. *)

Fixpoint eqblist (l1 l2 : natlist) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_eqblist1 :
  (eqblist nil nil = true).
 (* FILL IN HERE *) Admitted.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)

(** **** Exercise: 1 star, standard (count_member_nonzero) *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The following lemma about [leb] might help you in the next
    exercise (it will also be useful in later chapters). *)

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** Before doing the next exercise, make sure you've filled in the
   definition of [remove_one] above. *)
(** **** Exercise: 3 stars, advanced (remove_does_not_increase_count) *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (bag_count_sum)

    Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it using
    Coq.  (You may find that the difficulty of the proof depends on
    how you defined [count]!  Hint: If you defined [count] using
    [=?] you may find it useful to know that [destruct] works on
    arbitrary expressions, not just simple identifiers.)
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, advanced (involution_injective) *)

(** Prove that every involution is injective. Involutions were defined
    above in [rev_involutive]. An _injective_ function is one-to-one:
    it maps distinct inputs to distinct outputs, without any
    collisions. *)

Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, advanced (rev_injective)

    Prove that [rev] is injective. Do not prove this by induction --
    that would be hard. Instead, re-use the same proof technique that
    you used for [involution_injective]. Do not try to use that
    exercise directly as a lemma: the types are not the same. *)

Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Options *)

(** Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.

(** This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(** We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. As we see here, constructors of inductive definitions can
    be capitalized. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)
*)

(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Exercise: 2 stars, standard (hd_error)

    Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 1 star, standard, optional (option_elim_hd)

    This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id (n : nat).

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us flexibility to change representations later
    if we want to. *)

(** We'll also need an equality test for [id]s: *)

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(** **** Exercise: 1 star, standard (eqb_id_refl) *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
(* Export NatList.  make the definitions from NatList available here *)

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
    partial map by shadowing it with a new one (or simply adds a new
    entry if the given key is not already present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(** **** Exercise: 1 star, standard (update_eq) *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (update_neq) *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)
End PartialMap.

(** **** Exercise: 2 stars, standard, optional (baz_num_elts)

    Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

(** How _many_ elements does the type [baz] have? (Explain in words,
    in a comment.) *)

(* FILL IN HERE *)

(** [] *)

(* 2022-08-08 17:13 *)


(* ここから *)
Inductive list(X: Type) :=
    | Nil'
    | Cons'(x: X)(l: list X)
    .

Compute (Cons' nat 3 (Nil' nat)) : list nat.

Check Nil' : forall X : Type, list X.

(* Type -> Type で、 Xを受け取って、何かしらの(List関連の)型を返す *)
Check list.
(* List X 型  *)
Check Nil'.
(* List nat 型*)
Check Nil' nat.
(* X -> list X -> list X 型*)
Check Cons'.
Check Cons' nat.
Check Cons' nat O.
Check Cons'
        nat (* 型引数 *)
        O   (* head の要素 *)
        (Nil' nat). (* tail の要素. Nil'にも型注釈をつける. *)

Check Cons'
        nat
        O
        (Cons'
            nat
            (S O)
            (Nil' nat)).

Check (Cons' nat 2 (Cons' nat 1 (Nil' nat))).

(* Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
end. *)

Check Cons'.
(* 多相型の関数定義の例 *)
Fixpoint repeat'(X : Type)(x : X)(times : nat) : list X :=
    match times with
    | 0    => Nil' X
    | S n' => Cons' X x (repeat'(X)(x)(n'))
    end
.

Compute repeat'(nat)(7)(3).
