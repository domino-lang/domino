(defvar domino-keywords nil "lsl keywords")
(setq domino-keywords '("if" "else" "package" "composition" "theorem" "params" "state" "const" "oracle" "assert" "and" "or" "return" "fn" "compose" "adversary" "instance" "assumptions" "gamehops" "equivalence" "invariant" "lemmas" "reduction" "map" "assumption" "propositions"))

(defvar domino-types nil "lsl types")
(setq domino-types '("Bool" "Integer" "Bits" "Table"))

(defvar domino-constants nil "lsl constants")
(setq domino-constants '("true" "false" "None" "Some"))

(defvar domino-events nil "lsl events")
(setq domino-events '())

(defvar domino-functions nil "lsl functions")
(setq domino-functions '())

(defvar domino-fontlock nil "list for font-lock-defaults")

(setq domino-fontlock
      (let (dkeywords-regex dtypes-regex dconstants-regex devents-regex)

        ;; generate regex for each category of keywords
        (setq dkeywords-regex (regexp-opt domino-keywords 'words))
        (setq dtypes-regex (regexp-opt domino-types 'words))
        (setq dconstants-regex (regexp-opt domino-constants 'words))
        (setq devents-regex (regexp-opt domino-events 'words))
        (setq dfunctions-regex (regexp-opt domino-functions 'words))

        ;; note: order matters, because once colored, that part won't change. In general, put longer words first
        (list (cons dtypes-regex 'font-lock-type-face)
              (cons dconstants-regex 'font-lock-constant-face)
              (cons devents-regex 'font-lock-builtin-face)
              (cons dfunctions-regex 'font-lock-function-name-face)
              (cons dkeywords-regex 'font-lock-keyword-face))))



;;;###autoload
(define-derived-mode domino-mode c-mode "domino mode"
  "Major mode for editing Linden Scripting Language"

  ;; code for syntax highlighting
  (setq font-lock-defaults '((domino-fontlock))))

(add-to-list 'auto-mode-alist '("\\.ssp" . domino-mode))

;; add the mode to the `features' list
(provide 'domino-mode)
