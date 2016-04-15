(ns kangaroo.core
  (:require [clojure.string :as string]))

;TODO change name to barbara !!

; possible node types
(def ^:const ^:private END :end) ; no arrows out. FINAL state
(def ^:const ^:private SPLIT :split) ; unlabeled arrows to out and out1 (if != NULL)
(def ^:const ^:private LITERAL :literal) ; one arrow out. Only out is (checker %) is true

; HACK there be dragons !!
(defn- mk-id [] (hash #()))

(defrecord node       [id pred out out1]) ; one arrow out. Only out is (checker %) is true
(defrecord split-node [id out out1]) ; unlabeled arrows in out and out1 (if != NULL)

(defrecord nfa      [fid nodes])
(defrecord verdict  [ok? message])

;; (def ^:const ^:private END (->node 0 nil nil nil))

(defprotocol NfaPlugable "protocol definition required to convert a certain
  type into an NFA"
  (automat [object] "takes an object and wraps it in an NFA"))

(defprotocol Mechanic "protocol for patching up nodes with dangling out*"
  (connect [node id] "set a dangling out* in node to id"))

(defprotocol Statement "protocol to compare a certain input against"
  (holds? [object input] "check if the input holds against the object rules"))

;; (defprotocol Judgment "protocol to judge whether the result of a Statement
;;   holds or not"
;;   (judge [result] "judge whether or not result is true or false"))

;; (defprotocol Reporter "protocol for wrapping up the results of a failed statement"
;;   (trace [result] "trace why did a judment failed based on source"))

(extend-type nfa
  NfaPlugable
  (automat [object] object)
  Statement
  (holds? [object input] (->verdict false "FIXME"))) ;FIXME implement the whole NFA checking process here

(extend-type node
  NfaPlugable
  (automat [object] (->nfa (:id object) :content {(:id object) object}))
  Statement
  (holds? [object input] (if ((:pred object) input)
                           (->verdict true nil) ;FIXME make a named field and output that
                           (->verdict false (str "Expected " (:pred object)
                                                 " instead got: " input))))
  Mechanic
  (connect [object id] (if (nil? (:out object))
                         {(:id object) (assoc object :out id)}
                         {(:id object) object})))

(extend-type split-node
  Statement
  (holds? [object input] nil)
  Mechanic
  (connect [object id] (if (nil? (:out1 object))
                         {(:id object) (assoc object :out1 id)}
                         {(:id object) object})))

(extend-type clojure.lang.IFn
  NfaPlugable
  (automat [object] (automat (->node (mk-id) object nil nil))))

(extend-type java.lang.Object
  NfaPlugable
  (automat [object] (automat (->node (mk-id) #(= % object) nil nil))))

;; (defn- name-it
;;   "given a checker function and a state type return the unmangled function name"
;;   [checker stype]
;;   (cond (= stype END) "END"
;;         (nil? checker) nil
;;         :else (string/replace (second (re-find #"^.+\$(.+)\@.+$" (str checker)))
;;                               #"\_QMARK\_" "?")))

(defn- state
  "an NFA state with eps transitions. flag is one of LITERAL, SPLIT or END.
   Split states have no checker nor name. out and out1 are the states to follow
  if the checker condition is true."
  ([checker] (state checker nil nil LITERAL))
  ([checker out out1 flag]
   {:id (mk-id),; :name (name-it checker flag)
    :type flag, :checker checker, :out out, :out1 out1}))

; A partially built NFA. ':start' is the id of the start state
; ':content' is a hash-map of id-state of all the states in this automaton
(defn- automaton
  "encapsulation of NonDeterministic Finite State Automaton. Start is the
  id of the start state of the complete automaton: only one state allowed.
  content is a hash-map with all the states that the automaton contains."
  ([stat] {:start (:id stat) :content {(:id stat) stat}})
  ([start-id content] {:start start-id, :content content}))

(defn- patch
  "given a state and an out-id set the out or out1 value to out-id if non have
  been set yet."
  [stat out-id]
  (cond (and (= (:type stat) SPLIT) (nil? (:out1 stat)))
          [(:id stat) (assoc stat :out1 out-id)]
        (and (= (:type stat) LITERAL) (nil? (:out stat)))
          [(:id stat) (assoc stat :out out-id)]
    :default [(:id stat) stat]))

(defn cat
  "concatenate two or more automatons or functions."
  ([auto1 auto2]
   (cond
     (and (fn? auto1) (fn? auto2)) (cat (automaton (state auto1))
                                        (automaton (state auto2)))
     (fn? auto1) (cat (automaton (state auto1)) auto2)
     (fn? auto2) (cat auto1 (automaton (state auto2)))
     :default (let [new-states (into (hash-map) (map patch (vals (:content auto1))
                                                     (repeat (:start auto2))))]
                (assoc auto1 :content (merge new-states (:content auto2))))))
  ([auto1 auto2 & more-autos]
   (reduce cat (cat auto1 auto2) more-autos)))

(defn alt
  "alternate between two or more automatons or functions. "
  ([auto1 auto2]
   (cond
     (and (fn? auto1) (fn? auto2)) (alt (automaton (state auto1))
                                        (automaton (state auto2)))
     (fn? auto1) (alt (automaton (state auto1)) auto2)
     (fn? auto2) (alt auto1 (automaton (state auto2)))
     :default (let [split-st (state nil (:start auto1) (:start auto2) SPLIT)]
                (automaton (:id split-st) (merge (:content auto1)
                                                 {(:id split-st) split-st}
                                                 (:content auto2))))))
  ([auto1 auto2 & more-autos]
   (reduce alt (alt auto1 auto2) more-autos)))

(defn opt
  "optional function or automaton."
  [automat]
  (if (fn? automat) (opt (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:id split-st) (merge (:content automat)
                                       {(:id split-st) split-st})))))

(defn rep*
  "zero or more repetitions of the function or automaton"
  [automat]
  (if (fn? automat) (rep* (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:id split-st) (merge (into (hash-map) (map patch (vals (:content automat))
                                                             (repeat (:id split-st))))
                                       {(:id split-st) split-st})))))

(defn rep+
  "one or more repetitions of the function or automaton"
  [automat]
  (if (fn? automat) (rep+ (automaton (state automat)))
    (let [split-st (state nil (:start automat) nil SPLIT)]
      (automaton (:start automat) (merge (into (hash-map) (map patch (vals (:content automat))
                                                               (repeat (:id split-st))))
                                         {(:id split-st) split-st})))))

(defn- follow-link
  "given a state and a hash-map with all possible states, return the states
  that stat leads to."
  [stat auto-content]
  (if (= (:type stat) SPLIT)
      (into (follow-link (auto-content (:out stat)) auto-content)
            ;(follow-link auto-content)
            (follow-link (auto-content (:out1 stat)) auto-content))
      (hash-set (auto-content (:id stat)))))

(defn- next-states
  "given a sequence of states and a hash-map with all possible states, return
  the sequence of all states that 'states' lead to (not necesarily in order)."
  [states auto-content]
  (let [all-out  (map #(auto-content (:out %)) states)
        out-groups (group-by :type all-out)]
    (concat (LITERAL out-groups)
            (mapcat follow-link (SPLIT out-groups) (repeat auto-content))
            (distinct (END out-groups)))))

(defn- matching-states?
  "check if the given input matches the checker function probided in the state."
  [input stat]
  (when (= (:type stat) LITERAL)
    ((:checker stat) (first input))))

(defn- missing-input?
  "check there are still states to be matched but no more input to process."
  [input states]
  (and (empty? input) (not-empty states)))

(defn- extra-input?
  "check if the end of the automaton was reached but there is still input to process"
  [input states]
  (and (= (count states) 1) (= END (:type (first states))) (not-empty input)))

(defn- match?
  "check if a sucessfull end of the automaton was reached"
  [input states]
  (and (some #(= END (:type %)) states) (empty? input)))

(defn- error
  "returns a string with the error message of an unsucessfull match"
  [error-type input states]
  (condp = error-type
    :extra (str "too many elements: " (str input))
    :missing (str "missing elements: \n Expected any of "
                  (string/join ", " (map #(str (:checker %))  states)))
    :mismatch (str "Expected any of: " (string/join ", " (map #(str (:checker %)) states))
                   "; instead got: " (str input))))

(defn- step
  "traverse the automaton step by step checking if the input given matches
  the checkers function of the current sequence of states"
  [automat input states]
  (cond
    (extra-input? input states)   {:match false, :msg (error :extra input states)}
    (match? input states)         {:match true,  :msg nil}
    (missing-input? input states) {:match false, :msg (error :missing input states)}
    :default (if-let [matches (seq (filter #(matching-states? input %) states))]
               (recur automat (rest input) (next-states matches (:content automat)))
               {:match false, :msg (error :mismatch input states)})))

(defn exec
  "compares the provided regular expression to the given input. returns a hash-map
  with :match and :msg as the veredict of the match and an error message if the match
  was not sucessfull."
  [automat input]
  (let [final-machine (cat automat (automaton (state nil nil nil END)))
        start-state   (follow-link (get-in final-machine [:content (:start automat)])
                                   (:content final-machine))]
    (step final-machine input start-state)))

(def foo (alt (rep+ string?) list? map?))

(exec foo '("hello" (a b) "world"))

;(def b4 "/9j/4AAQSkZJRgABAQAAAQABAAD/4QBoRXhpZgAASUkqAAgAAAADABIBAwABAAAAAQAAADEBAgAQAAAAMgAAAGmHBAABAAAAQgAAAAAAAABTaG90d2VsbCAwLjE4LjAAAgACoAkAAQAAAKUBAAADoAkAAQAAAKQAAAAAAAAA/+ELzmh0dHA6Ly9ucy5hZG9iZS5jb20veGFwLzEuMC8APD94cGFja2V0IGJlZ2luPSLvu78iIGlkPSJXNU0wTXBDZWhpSHpyZVN6TlRjemtjOWQiPz4gPHg6eG1wbWV0YSB4bWxuczp4PSJhZG9iZTpuczptZXRhLyIgeDp4bXB0az0iWE1QIENvcmUgNC40LjAtRXhpdjIiPiA8cmRmOlJERiB4bWxuczpyZGY9Imh0dHA6Ly93d3cudzMub3JnLzE5OTkvMDIvMjItcmRmLXN5bnRheC1ucyMiPiA8cmRmOkRlc2NyaXB0aW9uIHJkZjphYm91dD0iIiB4bWxuczp4bXA9Imh0dHA6Ly9ucy5hZG9iZS5jb20veGFwLzEuMC8iIHhtbG5zOnhtcE1NPSJodHRwOi8vbnMuYWRvYmUuY29tL3hhcC8xLjAvbW0vIiB4bWxuczpzdFJlZj0iaHR0cDovL25zLmFkb2JlLmNvbS94YXAvMS4wL3NUeXBlL1Jlc291cmNlUmVmIyIgeG1sbnM6ZXhpZj0iaHR0cDovL25zLmFkb2JlLmNvbS9leGlmLzEuMC8iIHhtbG5zOnRpZmY9Imh0dHA6Ly9ucy5hZG9iZS5jb20vdGlmZi8xLjAvIiB4bXA6Q3JlYXRvclRvb2w9IkFkb2JlIFBob3Rvc2hvcCBDQyBNYWNpbnRvc2giIHhtcE1NOkluc3RhbmNlSUQ9InhtcC5paWQ6REY3NzQ3MDdCMTZCMTFFMzlFMEFEQzc2REMyOEE1MTEiIHhtcE1NOkRvY3VtZW50SUQ9InhtcC5kaWQ6REY3NzQ3MDhCMTZCMTFFMzlFMEFEQzc2REMyOEE1MTEiIGV4aWY6UGl4ZWxYRGltZW5zaW9uPSI0MjEiIGV4aWY6UGl4ZWxZRGltZW5zaW9uPSIxNjQiIHRpZmY6SW1hZ2VXaWR0aD0iNDIxIiB0aWZmOkltYWdlSGVpZ2h0PSIxNjQiIHRpZmY6T3JpZW50YXRpb249IjEiPiA8eG1wTU06RGVyaXZlZEZyb20gc3RSZWY6aW5zdGFuY2VJRD0ieG1wLmlpZDpERjc3NDcwNUIxNkIxMUUzOUUwQURDNzZEQzI4QTUxMSIgc3RSZWY6ZG9jdW1lbnRJRD0ieG1wLmRpZDpERjc3NDcwNkIxNkIxMUUzOUUwQURDNzZEQzI4QTUxMSIvPiA8L3JkZjpEZXNjcmlwdGlvbj4gPC9yZGY6UkRGPiA8L3g6eG1wbWV0YT4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICA8P3hwYWNrZXQgZW5kPSJ3Ij8+/9sAQwADAgIDAgIDAwMDBAMDBAUIBQUEBAUKBwcGCAwKDAwLCgsLDQ4SEA0OEQ4LCxAWEBETFBUVFQwPFxgWFBgSFBUU/9sAQwEDBAQFBAUJBQUJFA0LDRQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQU/8AAEQgApAGlAwEiAAIRAQMRAf/EAB8AAAEFAQEBAQEBAAAAAAAAAAABAgMEBQYHCAkKC//EALUQAAIBAwMCBAMFBQQEAAABfQECAwAEEQUSITFBBhNRYQcicRQygZGhCCNCscEVUtHwJDNicoIJChYXGBkaJSYnKCkqNDU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6g4SFhoeIiYqSk5SVlpeYmZqio6Slpqeoqaqys7S1tre4ubrCw8TFxsfIycrS09TV1tfY2drh4uPk5ebn6Onq8fLz9PX29/j5+v/EAB8BAAMBAQEBAQEBAQEAAAAAAAABAgMEBQYHCAkKC//EALURAAIBAgQEAwQHBQQEAAECdwABAgMRBAUhMQYSQVEHYXETIjKBCBRCkaGxwQkjM1LwFWJy0QoWJDThJfEXGBkaJicoKSo1Njc4OTpDREVGR0hJSlNUVVZXWFlaY2RlZmdoaWpzdHV2d3h5eoKDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uLj5OXm5+jp6vLz9PX29/j5+v/aAAwDAQACEQMRAD8A/VOiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAopM0tABRRSZoAWiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKKKKACiiigAooooAKazqilmIUDqTRJIsUbO7BEUZZmOAB3Jr4w8N6fq37bF58SteuL8W/hnTxJonhGxuQ7WaT7TuvpY0ZfMkAKFckhd3AyOQD7QDAgEHIPIxUd1dQ2VtLcXEqQW8KGSSWVgqIoGSxJ4AA5JNcB8AvhZcfBj4V6N4Tu9Yl165shI0l5JkAs7lyqBiSEXdgAk9K5H9sTVBo3wejv7yyn1Lw7bazp02vWkCFvO05bhDOrAdUwBkdxkHgmgD0XwZ8WvBfxEurq28MeKdJ165teZorC7SVkHrgHOPfpTLL4w+BtR8Xy+FrXxbo1x4jiYo+mR3sbThh1Xbn7w7r14PHFfJn7RmteA/H154c1z4Kamt/wDFi1jaa2Pg7AmbTghE4uGUARgIcLu+bcQoU54TxHB8E/iB+zlo1x8O7DTNJ8Zw3NquhWdqFXWYNUEyfu3P+tds7t7vkY3OTgZoA+480tRxBtibyC4HJHr3qSgAooooAKKKKACiikzzQAtFFFABRRRQAUUUUAFFFFABRRRQAUUUUAFIelLXKfFXx7a/C/4c+IfFV2hli0u0edYR1mk6Rxj3dyqj3YUAcL4k/af0LQvFOr6HY+F/GHiqXSZRbXl54d0dry2in2hmhMgYDeoZdw7ZFZv/AA1naf8ARLvid/4TLf8Axddb8A/A03wx+E2l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")
;b4
