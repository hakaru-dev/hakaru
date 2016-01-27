;;; Hakaru Mode
(setq myKeywords
 '(("#.*$" . font-lock-comment-face)
   ("return\\|True\\|False" . font-lock-constant-face)
   ("\\(\\w+\\)\\s-*\(" . (1 font-lock-function-name-face))		
   ("\"\\.\\*\\?" . font-lock-string-face)		
       ;; ; : , ; { } =>  @ $ = are all special elements
   ("def\\|fn\\|if\\|else\\|\sin\s"
    . font-lock-keyword-face)
   ("\\([~^<>=.\\+*/%-]\\)" 0 'font-lock-variable-name-face)
   ("nat\\|int\\|prob\\|real" . font-lock-type-face)))

(define-derived-mode hakaru-lang-mode fundamental-mode
  (setq font-lock-defaults '(myKeywords))
  (setq mode-name "Hakaru"))

(autoload 'hakaru-lang-mode "Hakaru" nil t)
(add-to-list 'auto-mode-alist '("\\.hk$" . hakaru-lang-mode))

