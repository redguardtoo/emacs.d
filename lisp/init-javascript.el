;; -*- coding: utf-8; lexical-binding: t; -*-

(setq-default js2-use-font-lock-faces t
              js2-mode-must-byte-compile nil
              ;; {{ comment indention in modern frontend development
              javascript-indent-level 2
              js-indent-level 2
              css-indent-offset 2
              typescript-indent-level 2
              ;; }}
              js2-strict-trailing-comma-warning nil ; it's encouraged to use trailing comma in ES6
              js2-idle-timer-delay 0.5 ; NOT too big for real time syntax check
              js2-auto-indent-p nil
              js2-indent-on-enter-key nil ; annoying instead useful
              js2-skip-preprocessor-directives t
              js2-strict-inconsistent-return-warning nil ; return <=> return null
              js2-enter-indents-newline nil
              js2-bounce-indent-p t)

(with-eval-after-load 'js-mode
  ;; '$' is part of variable name like '$item'
  (modify-syntax-entry ?$ "w" js-mode-syntax-table))

(defun my-validate-json-or-js-expression (&optional not-json-p)
  "Validate buffer or select region as JSON.
If NOT-JSON-P is not nil, validate as Javascript expression instead of JSON."
  (interactive "P")
  (let* ((json-exp (if (region-active-p) (my-selected-str)
                     (my-buffer-str)))
         (jsbuf-offet (if not-json-p 0 (length "var a=")))
         errs
         first-err
         (first-err-pos (if (region-active-p) (region-beginning) 0)))
    (unless not-json-p
      (setq json-exp (format "var a=%s;"  json-exp)))
    (with-temp-buffer
      (insert json-exp)
      (my-ensure 'js2-mode)
      (js2-parse)
      (setq errs (js2-errors))
      (cond
       ((not errs)
        (message "NO error found. Good job!"))
       (t
        ;; yes, first error in buffer is the last element in errs
        (setq first-err (car (last errs)))
        (setq first-err-pos (+ first-err-pos (- (cadr first-err) jsbuf-offet)))
        (message "%d error(s), first at buffer position %d: %s"
                 (length errs)
                 first-err-pos
                 (js2-get-msg (caar first-err))))))
    (if first-err (goto-char first-err-pos))))

(defun my-print-json-path (&optional hardcoded-array-index)
  "Print the path to the JSON value under point, and save it in the kill ring.
If HARDCODED-ARRAY-INDEX provided, array index in JSON path is replaced with it."
  (interactive "P")
  (cond
   ((memq major-mode '(js2-mode))
    (js2-print-json-path hardcoded-array-index))
   (t
    (let* ((cur-pos (point))
           (str (my-buffer-str)))
      (when (string= "json" (file-name-extension buffer-file-name))
        (setq str (format "var a=%s;" str))
        (setq cur-pos (+ cur-pos (length "var a="))))
      (my-ensure 'js2-mode)
      (with-temp-buffer
        (insert str)
        (js2-init-scanner)
        (js2-do-parse)
        (goto-char cur-pos)
        (js2-print-json-path))))))

(with-eval-after-load 'js2-mode
  ;; I hate the hotkeys to hide things
  (define-key js2-mode-map (kbd "C-c C-e") nil)
  (define-key js2-mode-map (kbd "C-c C-s") nil)
  (define-key js2-mode-map (kbd "C-c C-f") nil)
  (define-key js2-mode-map (kbd "C-c C-t") nil)
  (define-key js2-mode-map (kbd "C-c C-o") nil)
  (define-key js2-mode-map (kbd "C-c C-w") nil))
;; }}

(defun my-js2-mode-setup()
  "Set up javascript."
  (unless (is-buffer-file-temp)
    ;; if use node.js we need nice output
    (js2-imenu-extras-mode)
    (setq mode-name "JS2")
    ;; counsel/ivy is more generic and powerful for refactoring
    ;; js2-mode has its own syntax linter

   ;; call js-doc commands through `counsel-M-x'!

    ;; @see https://github.com/mooz/js2-mode/issues/350
    (setq forward-sexp-function nil)))

(add-hook 'js2-mode-hook 'my-js2-mode-setup)

;; @see https://github.com/felipeochoa/rjsx-mode/issues/33
(with-eval-after-load 'rjsx-mode
  (define-key rjsx-mode-map "<" nil))

;; {{ js-beautify
(defun js-beautify (&optional indent-size)
  "Beautify selected region or whole buffer with js-beautify.
INDENT-SIZE decide the indentation level.
`sudo pip install jsbeautifier` to install js-beautify.'"
  (interactive "P")
  (let* ((js-beautify (if (executable-find "js-beautify") "js-beautify"
                        "jsbeautify")))
    ;; detect indentation level
    (unless indent-size
      (setq indent-size (cond
                         ((memq major-mode '(js-mode javascript-mode))
                          js-indent-level)

                         ((memq major-mode '(web-mode))
                          web-mode-code-indent-offset)

                         ((memq major-mode '(typescript-mode))
                          typescript-indent-level)

                         (t
                          2))))
    ;; do it!
    (run-cmd-and-replace-region (concat "js-beautify"
                                        " --stdin "
                                        " --jslint-happy --brace-style=end-expand --keep-array-indentation "
                                        (format " --indent-size=%d " indent-size)))))
;; }}

;; {{ js-comint
(defun my-js-clear-send-buffer ()
  (interactive)
  (js-comint-clear)
  (js-comint-send-buffer))
;; }}

;; Latest rjsx-mode does not have indentation issue
;; @see https://emacs.stackexchange.com/questions/33536/how-to-edit-jsx-react-files-in-emacs
(setq-default js2-additional-externs
              '("$"
                "$A" ; salesforce lightning component
                "$LightningApp" ; salesforce
                "AccessifyHTML5"
                "Blob"
                "FormData"
                "KeyEvent"
                "Raphael"
                "React"
                "URLSearchParams"
                "__dirname" ; Node
                "_content" ; Keysnail
                "after"
                "afterEach"
                "angular"
                "app"
                "assert"
                "assign"
                "before"
                "beforeEach"
                "browser"
                "by"
                "clearInterval"
                "clearTimeout"
                "command" ; Keysnail
                "content" ; Keysnail
                "decodeURI"
                "define"
                "describe"
                "display" ; Keysnail
                "documentRef"
                "element"
                "encodeURI"
                "expect"
                "ext" ; Keysnail
                "fetch"
                "gBrowser" ; Keysnail
                "global"
                "goDoCommand" ; Keysnail
                "hook" ; Keysnail
                "inject"
                "isDev"
                "it"
                "jest"
                "jQuery"
                "jasmine"
                "key" ; Keysnail
                "ko"
                "log"
                "mockStore"
                "module"
                "mountWithTheme"
                "plugins" ; Keysnail
                "process"
                "require"
                "setInterval"
                "setTimeout"
                "shell" ; Keysnail
                "tileTabs" ; Firefox addon
                "util" ; Keysnail
                "utag"))

(defun my-typescript-beginning-of-defun-hack (orig-func &rest args)
  "Overwrite typescript beginning detection."
  (ignore orig-func)
  (ignore args)
  (when (my-use-tags-as-imenu-function-p)
    (let* ((cands (counsel--imenu-candidates))
           closest
           )
      (setq closest (my-get-closest-imenu-item cands))
      (when closest
        (imenu closest)))))
(advice-add 'typescript-beginning-of-defun :around #'my-typescript-beginning-of-defun-hack)

;; {{ typescript
(defun typescript-mode-hook-setup ()
  "Set up `typescript-mode'."
  (when (my-use-tags-as-imenu-function-p)
    ;; use ctags to calculate imenu items
    (setq imenu-create-index-function
          'counsel-etags-imenu-default-create-index-function)))
(add-hook 'typescript-mode-hook 'typescript-mode-hook-setup)
;; }}

(defvar my-js-document-tagnames
  '(characterSet
    childElementCount
    children
    compatMode
    contentType
    currentScript
    defaultView
    designMode
    doctype
    documentElement
    documentURI
    documentURIObject
    domain
    domConfig
    embeds
    fgColor
    firstElementChild
    forms
    fullscreen
    fullscreenEnabled
    height
    hidden
    images
    implementation
    lastElementChild
    lastModified
    lastStyleSheetSet
    linkColor
    links
    location
    mozSyntheticDocument
    onabort
    onafterscriptexecute
    onanimationcancel
    onanimationend
    onanimationiteration
    onauxclick
    onbeforescriptexecute
    onblur
    oncancel
    oncanplay
    oncanplaythrough
    onchange
    onclick
    onclose
    oncontextmenu
    oncuechange
    ondblclick
    ondurationchange
    onended
    onerror
    onfocus
    onformdata
    onfullscreenchange
    onfullscreenerror
    ongotpointercapture
    oninput
    oninvalid
    onkeydown
    onkeypress
    onkeyup
    onload
    onloadeddata
    onloadedmetadata
    onloadend
    onloadstart
    onlostpointercapture
    onmousedown
    onmouseenter
    onmouseleave
    onmousemove
    onmouseout
    onmouseover
    onmouseup
    onoffline
    ononline
    onpause
    onplay
    onplaying
    onpointercancel
    onpointerdown
    onpointerenter
    onpointerleave
    onpointermove
    onpointerout
    onpointerover
    onpointerup
    onreset
    onresize
    onscroll
    onselect
    onselectionchange
    onselectstart
    onsubmit
    ontouchcancel
    ontouchstart
    ontransitioncancel
    ontransitionend
    onvisibilitychange
    onwheel
    origin
    pictureInPictureEnabled
    plugins
    popupNode
    preferredStyleSheetSet
    readyState
    referrer
    rootElement
    scripts
    scrollingElement
    selectedStyleSheetSet
    styleSheetSets
    timeline
    title
    tooltipNode
    visibilityState
    vlinkColor
    width
    xmlEncoding
    xmlVersion
    adoptNode
    append
    caretRangeFromPoint
    clear
    close
    createAttribute
    createCDATASection
    createComment
    createDocumentFragment
    createElement
    createElementNS
    createEntityReference
    createEvent
    createExpression
    createExpression
    createNodeIterator
    createNSResolver
    createNSResolver
    createProcessingInstruction
    createRange
    createTextNode
    createTouch
    createTouchList
    createTreeWalker
    enableStyleSheetsForSet
    evaluate
    evaluate
    execCommand
    exitFullscreen
    exitPictureInPicture
    exitPointerLock
    getBoxObjectFor
    getElementById
    getElementsByClassName
    getElementsByName
    getElementsByTagName
    getElementsByTagNameNS
    hasFocus
    hasStorageAccess
    importNode
    mozSetImageElement
    prepend
    queryCommandEnabled
    queryCommandSupported
    querySelector
    querySelector
    querySelectorAll
    querySelectorAll
    registerElement
    releaseCapture
    replaceChildren
    requestStorageAccess
    write
    writeln))

(defvar my-js-window-tagnames
  '(caches
    closed
    console
    controllers
    crossOriginIsolated
    crypto
    customElements
    defaultStatus
    devicePixelRatio
    dialogArguments
    directories
    document
    event
    frameElement
    frames
    fullScreen
    history
    indexedDB
    innerHeight
    innerWidth
    isSecureContext
    isSecureContext
    length
    localStorage
    location
    locationbar
    menubar
    mozAnimationStartTime
    mozInnerScreenX
    mozInnerScreenY
    mozPaintCount
    name
    navigator
    onabort
    onafterprint
    onanimationcancel
    onanimationend
    onanimationiteration
    onappinstalled
    onauxclick
    onbeforeinstallprompt
    onbeforeprint
    onbeforeunload
    onblur
    oncancel
    oncanplay
    oncanplaythrough
    onchange
    onclick
    onclose
    oncontextmenu
    oncuechange
    ondblclick
    ondevicelight
    ondevicemotion
    ondeviceorientation
    ondeviceorientationabsolute
    ondeviceproximity
    ondragdrop
    ondurationchange
    onended
    onerror
    onfocus
    onformdata
    ongamepadconnected
    ongamepaddisconnected
    ongotpointercapture
    onhashchange
    oninput
    oninvalid
    onkeydown
    onkeypress
    onkeyup
    onlanguagechange
    onload
    onloadeddata
    onloadedmetadata
    onloadend
    onloadstart
    onlostpointercapture
    onmessage
    onmessageerror
    onmousedown
    onmouseenter
    onmouseleave
    onmousemove
    onmouseout
    onmouseover
    onmouseup
    onmozbeforepaint
    onpaint
    onpause
    onplay
    onplaying
    onpointercancel
    onpointerdown
    onpointerenter
    onpointerleave
    onpointermove
    onpointerout
    onpointerover
    onpointerup
    onpopstate
    onrejectionhandled
    onreset
    onresize
    onscroll
    onselect
    onselectionchange
    onselectstart
    onstorage
    onsubmit
    ontouchcancel
    ontouchstart
    ontransitioncancel
    ontransitionend
    onunhandledrejection
    onunload
    onuserproximity
    onvrdisplayactivate
    onvrdisplayblur
    onvrdisplayconnect
    onvrdisplaydeactivate
    onvrdisplaydisconnect
    onvrdisplayfocus
    onvrdisplaypointerrestricted
    onvrdisplaypointerunrestricted
    onvrdisplaypresentchange
    onwheel
    opener
    origin
    outerHeight
    outerWidth
    pageXOffset
    pageYOffset
    parent
    performance
    personalbar
    pkcs11
    screen
    screenLeft
    screenTop
    screenX
    screenY
    scrollbars
    scrollMaxX
    scrollMaxY
    scrollX
    scrollY
    self
    sessionStorage
    sidebar
    speechSynthesis
    status
    statusbar
    toolbar
    top
    visualViewport
    window

    Methods

    alert
    atob
    back
    blur
    btoa
    cancelAnimationFrame
    cancelIdleCallback
    captureEvents
    clearImmediate
    clearInterval
    clearTimeout
    close
    confirm
    convertPointFromNodeToPage
    convertPointFromPageToNode
    createImageBitmap
    dump
    fetch
    find
    focus
    forward
    getAttention
    getComputedStyle
    getDefaultComputedStyle
    getSelection
    home
    matchMedia
    minimize
    moveBy
    moveTo
    open
    openDialog
    postMessage
    print
    prompt
    queueMicrotask
    releaseEvents
    requestAnimationFrame
    requestFileSystem
    requestIdleCallback
    resizeBy
    resizeTo
    routeEvent
    scroll
    scrollBy
    scrollByLines
    scrollByPages
    scrollTo
    setCursor
    setImmediate
    setInterval
    setTimeout
    showModalDialog
    sizeToContent
    stop
    updateCommands))

(defun my-update-tags-file (tags-file)
  "Update TAGS-FILE."
  (when (memq major-mode '(js-mode typescript-mode js2-mode))
    (let ((s1 (mapconcat (lambda (tagname) (counsel-etags-tag-line tagname tagname 0)) my-js-document-tagnames ""))
          (s2 (mapconcat (lambda (tagname) (counsel-etags-tag-line tagname tagname 0)) my-js-window-tagnames ""))
          (s3 (mapconcat (lambda (tagname) (counsel-etags-tag-line tagname tagname 0)) '(addEventListener
                                                                                         dispatchEvent
                                                                                         removeEventListener) "")))
      (counsel-etags-append-to-tags-file
       (list (cons "https://developer.mozilla.org/en-US/docs/Web/API/Document/%s" s1)
             (cons "https://developer.mozilla.org/en-US/docs/Web/API/Window/%s" s2)
             (cons "https://developer.mozilla.org/en-US/docs/Web/API/EventTarget/%s" s3))
       tags-file))))
(add-hook 'counsel-etags-after-update-tags-hook 'my-update-tags-file)

(provide 'init-javascript)
