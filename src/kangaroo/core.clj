(ns kangaroo.core
  (:refer-clojure :rename {cat clj-cat, and clj-and})
  (:require [clojure.string :as string]
            [clojure.main :refer [demunge]]))

;TODO change name to barbara !!

(defonce ^:private id-counter (atom 0))
(defn- mk-id [] (swap! id-counter inc))

(defn- pretty-demunge
  [fn-object]
  (let [dem-fn (demunge (str fn-object))
        pretty (second (re-find #"(.*?\/.*?)[\-\-|@].*" dem-fn))]
    (if pretty pretty dem-fn)))

(comment the drill goes like this\:
  we convert everything to an NFA\; those are composed of nodes, each one with
  a predicate to check an input against. we then connect those NFAs such that
  they form a single one. Nested NFAs are possible, thus checking if they match
  an input is conditional with the kind of object that we are checking against.
  Nested NFAs return a verdict object to avoid rechecking the input to build up
  an error message. we rely on an extensive use of polymorphism.
  Peace !)

;; =============================PROTOCOLS ===================================;;

(defprotocol NfaPlugable "protocol definition required to convert a certain
  type into an NFA"
  (->automat [object] "takes an object and wraps it in an NFA"))

(defprotocol Judment "protocol to compare an input against an object rules"
  (judge [object input] "judge is input fulfills object's rules. returns true or false"))

(defprotocol Statement
  (holds? [object] "check the result of a judgment"))

(defprotocol Bypasser "protocol to get the output of (split-)node"
  (peep [anode nodes] "return a hash-map of {id node} nodes that anode leads to"))

(defprotocol Mechanic "protocol for patching up nodes with dangling out*"
  (connect [node id] "set a dangling out* in node to id"))

;; ===================== RECORDS & POLYMORPHISM =============================;;

;; a verdict of comparing an input against an object rule(s)
(defrecord verdict  [match info]
  Statement
  (holds? [object] (:match object)))

(declare exec)
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
  Judment
  (judge [object input] (exec object (repeat (count (:nodes object)) input))))

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

;; ================= POLYMORPHISM CLOJURE TYPES =============================;;

(extend-type java.lang.Boolean
  Statement
  (holds? [object] object))

(extend-type clojure.lang.Delay
  Judment
  (judge [object input] (judge @object input)))

(extend-type clojure.lang.IFn ;FIXME: replace this with clojure.lang.Fn, and delete the special cases
  Judment
  (judge [object input] (object input))
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred object :name (pretty-demunge object)}))))

(extend-type java.lang.Object
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred #(= % object) :name (str object)}))))

;; special cases

;; For some reason, symbol is an instance of IFn
(extend-type clojure.lang.Symbol
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred #(= % object) :name (str object)}))))

;; wrap the keyword in an equal comparison to avoid calling it as a function
(extend-type clojure.lang.Keyword
  NfaPlugable
  (->automat [object] (->automat (map->node {:id (mk-id) :pred #(= % object) :name (str object)}))))

;; ========================= IMPLEMENTATION =================================;;

;;  SINGLETON object
(def ^:private END (map->node {:id 0 :name "END" :pred (fn [input] false)}))

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
  [object object2 & more]
  (let [machine  (reduce cat (cat object object2) more)
        mach-and (map->nfa-and {:fid (:fid machine) :nodes (:nodes machine)})
        nest     (->node (mk-id) nil mach-and nil)]
    (map->nfa {:fid (:id nest) :nodes (hash-map (:id nest) nest)})))

(defn subex ;; implemented as an NFA inside a node
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

(def ^:private one?     #(= 1 (count %)))
(def ^:private verdict? #(instance? kangaroo.core.verdict %))

(defn- stop?
  [states input]
  (let [end-found   (some #(= % END) states)
        empty-input (empty? input)]
    (cond
      ;; too much input, not enough states
      (clj-and end-found (one? states) (not empty-input))
        (->verdict false {:type :extra-input :input input})
      ;; success !
      (clj-and end-found empty-input)
        (->verdict true nil)
      ;; missing input
      (clj-and empty-input (not-empty states))
        (->verdict false {:type :missing-input :states states})
      :else nil))); continue

;; (defn- mismatch-error
;;   [input results states]
;;   (let [nfs   (filter verdict? results)
;;         fails (filter #(fn? (:pred %)) states)]
;;     (cond-> (->verdict false {:type :mismatch :input input})
;;       (seq nfs)   (assoc-in [:info :nested] nfs)
;;       (seq fails) (assoc-in [:info :states] fails)
;;       (not (and (seq nfs) (seq fails))) (assoc-in [:info :states] states))))

(defn- mismatch-error
  [input results states]
  (let [nfs    (filter verdict? results)
        fails  (filter #(fn? (:pred %)) states)
        delays (filter delay? states)]
    (cond
      (clj-and (seq nfs) (seq fails)) (->verdict false {:type :mismatch
                                        :input input :states fails :nested nfs})
      (seq nfs) (->verdict false {:type :mismatch :input input :nested nfs})
      :else (->verdict false {:type :mismatch :input input :states states}))))

(defn- traverse
  "traverse the state machine step by step checking if the input given fulfills
  the any of the current sequence of states"
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
  "compares the provided regular expression to the given input. returns a hash-map
  with :match and :info as the verdict of the match and an error message if the match
  was not sucessfull."
  [auto input]
  (let [machine (cat auto END)
        starts  (vals (peep (get-in machine [:nodes (:fid machine)])
                            (:nodes machine)))]
    (traverse machine input starts)))

;; (def foo (cat (rep* "hello") list? "world"))
;; (def foo (cat (and list? (subex (cat 1 3))) string?))

(defn- ->viewer
  [coll]
  (clojure.walk/postwalk
    #(cond (record? %) (into {} %)
           (fn? %)     (str %)
           :else %)     coll))

;; (->viewer (exec foo '((1 2) "hello")))
;; (->viewer (cat foo END))
