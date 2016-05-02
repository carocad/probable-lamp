(ns kangaroo.core
  "implementation of Thompson construction algorithm with a few tweaks,
  namely: replaced char comparison by predicates, introduction of 'and'
  and 'subex' expressions as nested NFA, and use of delayed expressions
  for recursive definitions"
  (:refer-clojure :rename {cat clj-cat, and clj-and})
  (:require [clojure.string :as string]
            [clojure.main :refer [demunge]]
            [clojure.walk :refer [postwalk]]))

(defonce ^:private id-counter (atom 0))
(defn- mk-id [] (swap! id-counter inc))

(defn- pretty-demunge
  [fn-object]
  (let [dem-fn (demunge (str fn-object))
        pretty (second (re-find #"(.*?\/.*?)[\-\-|@].*" dem-fn))]
    (if pretty pretty dem-fn)))

(comment the drill goes like this\:
  we convert everything to an NFA (Non-Deterministic Finite State
  Automat - with eps transitions)\; those are composed of nodes, each one has
  a predicate to check an input against. we then connect those NFAs such that
  they form a single one. Nested NFAs are possible, thus checking if they match
  an input is conditional with the kind of object that we are checking against.
  Nested NFAs return an error object when they fail to avoid rechecking the input
  to build up an error message. we rely on an extensive use of polymorphism.
  Peace !!)

;; NOTES: both Delays and NFA-and require mocking the input therefore an
;;        correction process is necessary to avoid reporting bad input

;; =============================PROTOCOLS ===================================;;

(defprotocol NfaPlugable "protocol definition required to convert a certain
  type into an NFA"
  (->automat [object] "takes an object and wraps it in an NFA"))

(defprotocol Judment "protocol to compare an input against an object rules"
  (judge [object input] "judge is input fulfills object's rules. returns true or false"))

(defprotocol Statement
  (holds? [object] "check the result of a judgment"))

(defprotocol Bypasser "protocol to get the output of a (split-)node"
  (peep [anode nodes] "return a hash-map of {id node} nodes that anode leads to"))

(defprotocol Mechanic "protocol for patching up nodes with dangling out*"
  (connect [node id] "set a dangling out* in node to id"))

;; ===================== RECORDS & POLYMORPHISM =============================;;

(declare exec); function to run an NFA rules against an input sequence, see below

;; a NonDeterministic Finite Automat with first node id fid and an integer
;; hash-map of nodes
(defrecord nfa [fid nodes]
  NfaPlugable
  (->automat [object] object)
  Judment
  (judge [object input] (exec object input)))

;; a NonDeterministic Finite Automat with first node id fid and an integer
;; hash-map of nodes. Contrary to nfa, nfa-and compares a single input against
;; all nodes
(defrecord nfa-and [fid nodes]
  NfaPlugable
  (->automat [object] object)
  Judment;;FIXME: fixing the input like that is not perfect, but it should do for the moment
  (judge [object input] (let [rinput (repeat (count (:nodes object)) input)
                              res    (exec object rinput)
                              correct (fn [err] (if (some->> (:input err) (every? #(= input %)))
                                                  (assoc err :input input)
                                                  err))]
                          (if (true? res) res
                            (postwalk correct res)))))

;; an NFA state with (possible) eps transitions, a predicate to compare input against,
;; and two possible output states
(defrecord node [id name pred out] ; one arrow out
  NfaPlugable
  (->automat [object] (map->nfa {:fid (:id object) :nodes (hash-map (:id object) object)}))
  Statement
  (holds? [object] object); no-op, return it as it is
  Bypasser ;; everything you want is here; no need to look for more ;)
  (peep [anode nodes] (apply hash-map (find nodes (:id anode))))
  Mechanic
  (connect [object id] (if (nil? (:out object))
                         (hash-map (:id object) (assoc object :out id))
                         (hash-map (:id object) object))))

;; an NFA state with *only* eps transitions and two possible output states
;; unlabeled arrows in out and out1 (if-not (nil? out*))
(defrecord split-node [id out out1]
  Mechanic
  (connect [object id] (if (nil? (:out1 object))
                         (hash-map (:id object) (assoc object :out1 id))
                         (hash-map (:id object) object)))
  Bypasser
  (peep [anode nodes] (merge (peep (get nodes (:out  anode)) nodes)
                             (when-let [arrow (:out1 anode)]
                               (peep (get nodes arrow) nodes)))))

;; an error with the information  of the states, input and kind of error that
;; happened
(defrecord error [type input states subex]
  Statement
  (holds? [object] false));; any error instance is a prove of failure

;; ================= POLYMORPHISM CLOJURE TYPES =============================;;

(extend-type java.lang.Boolean
  Statement
  (holds? [object] object))

(extend-type clojure.lang.Fn
  Judment
  (judge [object input] (object input))
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred object :name (pretty-demunge object)}))))

(extend-type clojure.lang.Delay
  Judment;;FIXME: wrappin/unwrapping the input like that is not perfect, but it should do for the moment
  (judge [object input] (let [rinput (repeat (count (:nodes object)) input)
                              res    (if (instance? kangaroo.core.nfa @object)
                                       (judge @object (list input)); wrap the input in a list to make it look as if passed directly
                                       (judge @object input))
                              correct (fn [err] (if (some->> (:input err) (= (list input)))
                                                  (assoc err :input input);;unwrap the input
                                                  err))]
                          (if (true? res) res
                            (postwalk correct res))))

  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred object})))); :name (pretty-demunge object), get the name at runtime !

(extend-type java.lang.Object; anything that is not a function is check for equality
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred #(= % object) :name (str object)}))))

;; ========================= IMPLEMENTATION =================================;;

;;  SINGLETON object, END of any nfa
(def END (map->node {:id 0 :name "END" :pred (fn [input] false)}))

(defn cat
  "concatenate two or more objects"
  ([object] (->automat object))
  ([object object2]
   (let [auto1 (->automat object)
         auto2 (->automat object2)
         new-states (apply merge (map connect (vals (:nodes auto1))
                                      (repeat (:fid auto2))))]
                (assoc auto1 :nodes (merge new-states (:nodes auto2)))))
  ([object object2 & more-objects]
   (reduce cat (cat object object2) more-objects)))

(defn alt
  "alternate between two or more objects"
  ([object object2]
   (let [auto1 (->automat object)
         auto2 (->automat object2)
         split (map->split-node {:id (mk-id) :out (:fid auto1) :out1 (:fid auto2)})]
     (map->nfa {:fid (:id split) :nodes (merge (:nodes auto1)
                                               (hash-map (:id split) split)
                                               (:nodes auto2))})))
  ([object object2 & more-objects]
   (reduce alt (alt object object2) more-objects)))

(defn opt
  "optional object"
  [object]
    (let [auto  (->automat object)
          split (map->split-node {:id (mk-id) :out (:fid auto)})]
      (map->nfa {:fid (:id split) :nodes (merge (:nodes auto) (hash-map (:id split) split))})))

(defn rep*
  "zero or more repetitions of the object"
  [object]
    (let [auto  (->automat object)
          split (map->split-node {:id (mk-id) :out (:fid auto)})]
      (map->nfa {:fid (:id split) :nodes (into (hash-map (:id split) split)
                                               (map connect (vals (:nodes auto))
                                                            (repeat (:id split))))})))

(defn rep+
  "one or more repetitions of the object"
  [object]
  (let [auto  (->automat object)
        split (map->split-node {:id (mk-id) :out (:fid auto)})]
    (map->nfa {:fid (:fid auto) :nodes (into (hash-map (:id split) split)
                                             (map connect (vals (:nodes auto))
                                                          (repeat (:id split))))})))

(defn and ;; implemented as an NFA-and inside a node
  "use this if the input should satisfy two or more conditions"
  [object object2 & more]
  (let [machine  (reduce cat (cat object object2) more)
        mach-and (map->nfa-and {:fid (:fid machine) :nodes (:nodes machine)})
        nest     (->node (mk-id) nil mach-and nil)]
    (map->nfa {:fid (:id nest) :nodes (hash-map (:id nest) nest)})))

(defn subex ;; implemented as an NFA inside a node
  "subexpression (or subpattern) matching. The elements inside the input
  should match the object rules"
  [object]
  (let [machine  (->automat object)
        nest     (->node (mk-id) nil machine nil)]
    (map->nfa {:fid (:id nest) :nodes (hash-map (:id nest) nest)})))

(defn- next-states
  "given a sequence of nodes (not split nodes) and a hash-map with all possible
  nodes, return the sequence of all states that 'states' lead to"
  [states nodes]
  (let [all-out  (map #(get nodes (:out %)) states)
        literals (filter :pred all-out)
        splits   (remove :pred all-out)]
    (distinct (concat literals (sequence (comp (map peep) (mapcat vals))
                                         splits (repeat nodes))))))

(def ^:private error? #(instance? kangaroo.core.error %))

(defn- stop?
  "stop traversing the NFA if a sucessfull match was found or if we ran out
  of input/states"
  [states input]
  (let [end-found   (some #(= % END) states)
        empty-input (empty? input)]
    (cond
      ;; too much input, not enough states
      (clj-and end-found (= 1 (count states)) (not empty-input))
        (map->error {:type :extra-input :input input})
      ;; success !
      (clj-and end-found empty-input) true
      ;; missing input
      (clj-and empty-input (not-empty states))
        (map->error {:type :missing-input :states states})
      :else nil))); continue

(defn- mismatch-error
  "returns a verdict object with error information"
  [input results states]
  ;; FIXME: if a state is a delay, its result should be separated from states
  (let [sub-nfs (filter error? results)
        fails   (filter #(fn? (:pred %)) states)]
    (cond
      (clj-and (seq sub-nfs) (seq fails)) (map->error {:type :mismatch
                                        :input input :states fails :subex sub-nfs})
      (seq sub-nfs) (map->error {:type :mismatch :input input :subex sub-nfs})
      :else (map->error {:type :mismatch :input input :states states}))))

(defn- traverse
  "traverse the state machine step by step checking if the input given fulfills
  any of the current sequence of states"
  [machine input states]
  (let [results (into [] (comp (map :pred) (map #(judge % (first input)))) states)
        matches (keep-indexed #(when (holds? (get results %1)) %2) states)
        todo    (next-states matches (:nodes machine))
        halt    (stop? todo (rest input))]
;;     (Thread/sleep 10000)
    (if (clj-and (not-empty todo) (not halt))
      (recur machine (rest input) todo)
      (if halt halt ; failure
        (mismatch-error input results states)))))

(defn exec
  "compares the provided regular expression to the given input. returns true if
  the input matches the provided rules, or an error object with the state at
  which the input failed the rules"
  [auto input]
  (let [machine (cat auto END)
        starts  (vals (peep (get-in machine [:nodes (:fid machine)])
                            (:nodes machine)))]
    (traverse machine input starts)))
