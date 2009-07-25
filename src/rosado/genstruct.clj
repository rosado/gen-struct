;;; genstruct

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

(defn- #^Class the-class [x]            ; copied from genclass.clj
  (cond 
    (class? x) x
    (contains? prim->class x) (prim->class x)
    :else (let [strx (str x)]
            (clojure.lang.RT/classForName 
             (if (some #{\.} strx)
               strx
               (str "java.lang." strx))))))

(defn generate-struct [options-map]
  (let [default-options {:load-impl-ns true :impl-ns (ns-name *ns*)}
        {:keys [name factory load-impl-ns impl-ns]} 
        (merge default-options options-map)
        name (str name)
        super Object
        cv (new ClassWriter (. ClassWriter COMPUTE_MAXS))
        cname (. name (replace "." "/"))
        pkg-name name
        impl-pkg-name (str impl-ns)
        impl-cname (.. impl-pkg-name (replace "." "/") (replace \- \_))
        ctype (. Type (getObjectType cname))
        iname (fn [#^Class c] (.. Type (getType c) (getInternalName)))
        totype (fn [#^Class c] (. Type (getType c)))
        emit-ctor (fn []
                    (let [m (Method/getMethod "void <init>()")
                          mg (new GeneratorAdapter (Opcodes/ACC_PUBLIC) m nil nil cv)]
                      (.loadThis mg)
                      (.invokeConstructor mg (totype super) m)
                      (.returnValue mg)
                      (.endMethod mg)))]
    (. cv (visit (. Opcodes V1_5) (+ (. Opcodes ACC_PUBLIC) (. Opcodes ACC_SUPER))
                 cname nil (iname super) nil))
    (emit-ctor)
    (. cv visitEnd )
    [cname (. cv (toByteArray))]))

(def test-options {:name 'rosado.genstruct.test
                   :factory nil
                   })

(binding [*compile-path* "c:/users/roland/dev/clojure/genstruct/target/classes"]
  (let [options-map test-options
        [cname bytecode] (generate-struct options-map)]
    (clojure.lang.Compiler/writeClassFile cname bytecode)))

(comment
  (defn- generate-struct []
    (let [default-options {:load-impl-ns true :impl-ns (ns-name *ns*)}
          {:keys [name factory load-impl-ns impl-ns]} 
          (merge default-options options-map)
          name (str name)
          super Object
          cv (new ClassWriter (. ClassWriter COMPUTE_MAXS))
          cname (. name (replace "." "/"))
          pkg-name name
          impl-pkg-name (str impl-ns)
          impl-cname (.. impl-pkg-name (replace "." "/") (replace \- \_))
          ctype (. Type (getObjectType cname))
          iname (fn [#^Class c] (.. Type (getType c) (getInternalName)))
          totype (fn [#^Class c] (. Type (getType c)))
          to-types (fn [cs] (if (pos? (count cs))
                              (into-array (map totype cs))
                              (make-array Type 0)))
          obj-type #^Type (totype Object)
          arg-types (fn [n] (if (pos? n)
                              (into-array (replicate n obj-type))
                              (make-array Type 0)))
          super-type #^Type (totype super)
          factory-name (str factory)
          var-name (fn [s] (str s "__var"))
          class-type  (totype Class)
          rt-type  (totype clojure.lang.RT)
          var-type #^Type (totype clojure.lang.Var)
          ifn-type (totype clojure.lang.IFn)
          iseq-type (totype clojure.lang.ISeq)
          ex-type  (totype java.lang.UnsupportedOperationException)
          var-fields (concat (distinct (concat (keys sigs-by-name)
                                               (mapcat (fn [[m s]] (map #(overload-name m (map the-class %)) s)) overloads)
                                               (mapcat (comp (partial map str) vals val) exposes))))
          emit-get-var (fn [#^GeneratorAdapter gen v]
                         (let [false-label (. gen newLabel)
                               end-label (. gen newLabel)]
                           (. gen getStatic ctype (var-name v) var-type)
                           (. gen dup)
                           (. gen invokeVirtual var-type (. Method (getMethod "boolean isBound()")))
                           (. gen ifZCmp (. GeneratorAdapter EQ) false-label)
                           (. gen invokeVirtual var-type (. Method (getMethod "Object get()")))
                           (. gen goTo end-label)
                           (. gen mark false-label)
                           (. gen pop)
                           (. gen visitInsn (. Opcodes ACONST_NULL))
                           (. gen mark end-label)))
          emit-unsupported (fn [#^GeneratorAdapter gen #^Method m]
                             (. gen (throwException ex-type (str (. m (getName)) " ("
                                                                 impl-pkg-name "/" prefix (.getName m)
                                                                 " not defined?)"))))
          emit-forwarding-method
          (fn [mname pclasses rclass as-static else-gen]
            (let [pclasses (map the-class pclasses)
                  rclass (the-class rclass)
                  ptypes (to-types pclasses)
                  rtype #^Type (totype rclass)
                  m (new Method mname rtype ptypes)
                  is-overload (seq (overloads mname))
                  gen (new GeneratorAdapter (+ (. Opcodes ACC_PUBLIC) (if as-static (. Opcodes ACC_STATIC) 0)) 
                           m nil nil cv)
                  found-label (. gen (newLabel))
                  else-label (. gen (newLabel))
                  end-label (. gen (newLabel))]
              (. gen (visitCode))
              (if (> (count pclasses) 18)
                (else-gen gen m)
                (do
                  (when is-overload
                    (emit-get-var gen (overload-name mname pclasses))
                    (. gen (dup))
                    (. gen (ifNonNull found-label))
                    (. gen (pop)))
                  (emit-get-var gen mname)
                  (. gen (dup))
                  (. gen (ifNull else-label))
                  (when is-overload
                    (. gen (mark found-label)))
                                        ;if found
                  (.checkCast gen ifn-type)
                  (when-not as-static
                    (. gen (loadThis)))
                                        ;box args
                  (dotimes [i (count ptypes)]
                    (. gen (loadArg i))
                    (. clojure.lang.Compiler$HostExpr (emitBoxReturn nil gen (nth pclasses i))))
                                        ;call fn
                  (. gen (invokeInterface ifn-type (new Method "invoke" obj-type 
                                                        (to-types (replicate (+ (count ptypes)
                                                                                (if as-static 0 1)) 
                                                                             Object)))))
                                        ;(into-array (cons obj-type 
                                        ;                 (replicate (count ptypes) obj-type))))))
                                        ;unbox return
                  (. gen (unbox rtype))
                  (when (= (. rtype (getSort)) (. Type VOID))
                    (. gen (pop)))
                  (. gen (goTo end-label))
                
                                        ;else call supplied alternative generator
                  (. gen (mark else-label))
                  (. gen (pop))
                
                  (else-gen gen m)
            
                  (. gen (mark end-label))))
              (. gen (returnValue))
              (. gen (endMethod))))
          ])))


(comment
  ;; usage example
  (gen-struct
   :name rosado.genstruct.example
   :fields [[static float MAX_HEIGHT]
            [float x]
            [float y]])
  ;; 
  (gen-class
   :name clojure.examples.impl
   :implements [clojure.examples.IBar]
   :prefix "impl-"
   :methods [[foo [] String]])
  )
