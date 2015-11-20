;;; test support functions for elnode

(require 'noflet)

(defmacro elnode-sink (httpcon &rest body)
  "Sink the HTTP response from BODY.

Output to `elnode-http-start', `elnode-http-send-string' and
`elnode-http-return' is collected and stored internallly.

When `elnode-http-return' is called the form ends with a string
result of whatever was sent as the response.  The string is
propertized with the header sent to `elnode-http-start'."
  (declare (indent 1)(debug (sexp &rest form)))
  `(let (res reshdr)
     (catch :elnode-sink-ret
       (noflet ((elnode-http-start (httpcon status &rest header)
                  (setq reshdr 
                        (kvalist->plist header)))
                (elnode-http-header-set (httpcon header &optional value)
                  (setq reshdr
                        (plist-put (intern (concat ":" reshdr))
                                   header value)))
                (elnode-http-send-string (httpcon data)
                  (setq res (apply 'propertize
                                   (concat res data) reshdr)))
                (elnode-http-return (httpcon &optional data)
                  (when data
                    (setq res (apply 'propertize
                                     (concat res data) reshdr)))
                  (throw :elnode-sink-ret :end)))
         ,@body))
     res))

(defmacro elnode-fake-params (httpcon params-list &rest body)
  "Fake the PARAM-BINDINGS and evaluate BODY.

PARAM-BINDINGS is an ALIST with string cars for parameter names
and string cdrs for values.  A cdr of a list can be used to
provide a string value with a property list, for example:

  '((\"param1\" . \"value\" )
    (\"param2\" \"value\" :elnode-filename \"somefile.txt\"))

Note the first parameter is an improper list.

PARAM-BINDINGS should be quoted."
  (declare (indent 2)
           (debug (sexp sexp &rest form)))
  `(let ((,httpcon ,params-list))
     (noflet ((elnode-http-param (httpc param-name)
                (if (eq httpc ,httpcon)
                    (let ((v (kva param-name ,httpcon)))
                      (cond
                        ((listp v)
                         (apply 'propertize (car v) (cdr v)))
                        (t v)))
                    (funcall this-fn httpcon param-name))))
       ,@body)))


(provide 'elnode-testsupport)

;;; elnode-testsupport.el ends here
