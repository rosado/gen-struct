;; Copyright (c) 2009 Roland Sadowski. All rights reserved.  The use and
;; distribution terms for this software are covered by the Common
;; Public License 1.0 (http://www.opensource.org/licenses/cpl1.0.php)
;; which can be found in the file CPL.TXT at the root of this
;; distribution.  By using this software in any fashion, you are
;; agreeing to be bound by the terms of this license.  You must not
;; remove this notice, or any other, from this software. 

;;; gen-struct macro and some of the helper functions are based
;;; on the code in genstruct.clj written by Rich Hickey, creator of Clojure.

(ns rosado.genstruct
  (:import (java.lang.reflect Modifier Constructor)
           (clojure.asm ClassWriter ClassVisitor Opcodes Type)
           (clojure.asm.commons Method GeneratorAdapter)))

(defn- escape-class-name [#^Class c]    ; copied from genclass.clj
  (.. (.getSimpleName c) 
      (replace "[]" "<>")))

(def #^{:private true} prim->class      ; copied from genclass.clj
     {'int Integer/TYPE
      'long Long/TYPE
      'float Float/TYPE
      'double Double/TYPE
      'void Void/TYPE
      'short Short/TYPE
      'boolean Boolean/TYPE
      'byte Byte/TYPE
      'char Character/TYPE})

(def #^{:private true} prim->desc
     {'int "I"
      'long "J"
      'float "F"
      'double "D"
      'short "S"
      'boolean "Z"
      'byte "B"
      'char "C"
      })

(defn- #^Class the-class [x]            ; copied from genclass.clj
  (cond 
    (class? x) x
    (contains? prim->class x) (prim->class x)
    :else (let [strx (str x)]
            (clojure.lang.RT/classForName 
             (if (some #{\.} strx)
               strx
               (str "java.lang." strx))))))

(defn- #^String the-descriptor[x]
  (cond
    (contains? prim->desc x) (prim->desc x)
    :else (Type/getDescriptor (the-class x))))

(defn- static? [fieldspec]
  (some #{'static} fieldspec))

(defn- validate-options [options]
  (let [{:keys [mutable-fields final-fields]} options
        volatile? #(some #{'volatile} %)]
    (when (some static? mutable-fields)
      (throw (new Exception "Can't create 'static' instance fields.")))
    (when (or (some volatile? mutable-fields)
              (some volatile? final-fields))
      (throw (new Exception "'volatile' is not supported")))))

(defn- generate-struct
  [options-map]
  (let [default-options {}
        {:keys [name mutable-fields final-fields]} 
        (merge default-options options-map)
        name (str name)
        super Object
        cv (new ClassWriter (. ClassWriter COMPUTE_MAXS))
        cname (. name (replace "." "/"))
        pkg-name name
        ctype (. Type (getObjectType cname))
        iname (fn [#^Class c] (.. Type (getType c) (getInternalName)))
        totype (fn [#^Class c] (. Type (getType c)))
        to-types (fn [cs] (if (pos? (count cs))
                            (into-array (map totype cs))
                            (make-array Type 0)))
        non-static-finals (filter (complement #(some #{'static} %)) final-fields)
        rm-static #(remove #{'static} %)
        emit-ctor (fn [args]
                    (let [argtypes (to-types (map first args))
                          m (new Method "<init>" (. Type VOID_TYPE) argtypes)
                          supm (new Method "<init>" (. Type VOID_TYPE) (to-types nil))
                          mg (new GeneratorAdapter (Opcodes/ACC_PUBLIC) m nil nil cv)]
                      (.loadThis mg)
                      (.invokeConstructor mg (totype super) supm)
                      (doseq [i (range (count args))]
                        (.loadThis mg)
                        (.loadArg mg i)
                        (.putField mg ctype (second (nth args i)) (aget argtypes i)))
                      (.returnValue mg)
                      (.endMethod mg)))
        emit-field (fn [access [type-symbol fld-name] & default-val]
                     (let [vl (if (and (seq default-val) (contains? prim->desc type-symbol))
                                (list type-symbol (first default-val))
                                (first default-val))
                           v (when vl (eval vl))]
                       (. cv (visitField access (str fld-name) (the-descriptor type-symbol) nil v))
                       (. cv visitEnd )))
        split-fields (fn [specs]
                       (loop [sp (first specs) specs (rest specs) st [] inst []]
                         (if sp
                           (if (static? sp)
                             (recur (first specs) (rest specs) (conj st (rm-static sp)) inst)
                             (recur (first specs) (rest specs) st (conj inst sp)))
                           [st inst])))
        [static+mutables mutables] (split-fields mutable-fields)
        [static+finals finals] (split-fields final-fields)
        ]
    (validate-options options-map)
    (. cv (visit (. Opcodes V1_5) (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_SUPER))
                 cname nil (iname super) nil))
    (when mutable-fields
      (doseq [spec mutables]
        (emit-field (. Opcodes ACC_PUBLIC) spec))
      (doseq [spec static+mutables]
        (emit-field (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_STATIC)) spec)))
    (when final-fields
      (doseq [spec finals]
        (emit-field (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_FINAL)) spec))
      (doseq [spec static+finals]
        (emit-field (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_FINAL) (. Opcodes ACC_STATIC))
                    (take 2 spec)
                    (last spec))))
    (emit-ctor (map (fn [[t n]] [(the-class t) (str n)]) finals))
    [cname (. cv (toByteArray))]))

(defmacro gen-struct
  "When compiling, generates compiled bytecode for a class with the
   given package-qualified :name (which, as all names in these
   parameters, can be a string or a symbol), and writes the .class
   file to the *compile-path* directory. When not compiling, does
   nothing. The gen-struct construct contains only instance and static
   fields.

  In all subsequent sections taking types, the primitive types can be
  referred to by their Java names (int, float etc), and classes in the
  java.lang package can be used without a package qualifier. All other
  classes must be fully qualified.

  :name aname

  The package-qualified name of the class to be generated.

  :mutable-fields

  A vector of field specs where a field spec is a vector of the form:

      [type name]

  Note that gen-struct does not allow for static non-final fields.

  :final-fields

  A vector of field specs where a field spec is a vector of the form:

      [type name] or [type static name :is value].

  Final non-static fields will have to be initialized by passing an
  appropriate argument to the constructor (in order the fields appear
  in the definition). 

  Final static fields can only be of one of the primitive types.

  Example:

  (gen-struct
    :name my.ns.struct
    :mutable-fields [[float x]
                     [float y]]
    :final-fields [[int timeout]
                   [static int MAX_TIMEOUT_MS :is 1000]
                   [java.io.File input]])
  "
  [& options]
  (when *compile-files*
    (let [options-map (apply hash-map options)
          [cname bytecode] (generate-struct options-map)]
      (clojure.lang.Compiler/writeClassFile cname bytecode))))

(comment
  (gen-struct
   :name rosado.genstruct.test111
   :mutable-fields [[float x]
                    [float y]]
   :final-fields [[static double K :is 23.0]
                  [static int MAX_X :is 1000]
                  [double maxAmount]])

  (gen-struct
   :name rosado.genstruct.test201
   :mutable-fields [[float x]
                    [float y]]
   :final-fields [[int timeout]
                  [static int MAX_TIMEOUT_MS :is 1000]
                  [java.io.File input]])
  )

