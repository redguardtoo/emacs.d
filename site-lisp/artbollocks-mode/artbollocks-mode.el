;;; artbollocks-mode.el --- Improve your writing (especially about art)
;;
;; Copyright (c) 2011,2012 Rob Myers <rob@robmyers.org>
;; Minor changes (c) 2012 Sacha Chua <sacha@sachachua.com>
;;
;; Author: Rob Myers <rob@robmyers.org>, Sacha Chua <sacha@sachachua.com>
;; URL: https://github.com/sachac/artbollocks-mode
;; Version: 1.1.2
;;
;; Based on fic-mode.el
;; Copyright (C) 2010, Trey Jackson <bigfaceworm(at)gmail(dot)com>
;;
;; Non-artbollocks words from: http://matt.might.net/articles/
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU Affero General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; at your option any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;; 2012-06-16: Renamed functions and variables to avoid collisions.
;; Incompatible changes, so please review your configuration. - Sacha
;; Chua
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extra thanks to:
;; Brian van den Broek (words: contextuality, dialetic, problematize)
;; Isabel Brison (words: alterity, mise en abîme)
;; mneilsen, behaghel, russell, xfq, gleb, ejmr, tarsius (Emacs Lisp improvements)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commentary:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Usage
;;
;; To use, save artbollocks-mode.el to a directory in your load-path.
;;
;; (require 'artbollocks-mode)
;; (add-hook 'text-mode-hook 'artbollocks-mode)
;;
;; or
;;
;; M-x artbollocks-mode
;;
;; NOTE: If you manually turn on artbollocks-mode,
;; you you might need to force re-fontification initially:
;;
;;   M-x font-lock-fontify-buffer
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Enable features individually

(defcustom artbollocks-lexical-illusions t
  "Whether to check for lexical illusions"
  :type '(boolean)
  :group 'artbollocks-mode)

(defcustom artbollocks-passive-voice t
  "Whether to check for passive voice"
  :type '(boolean)
  :group 'artbollocks-mode)

(defcustom artbollocks-weasel-words t
  "Whether to check for weasel words"
  :type '(boolean)
  :group 'artbollocks-mode)

(defcustom artbollocks-jargon t
  "Whether to check for artbollocks jargon"
  :type '(boolean)
  :group 'artbollocks-mode)

(defface artbollocks-lexical-illusions-face
  '((t (:foreground "black" :background "magenta")))
  "The face for lexical illusions words"
  :group 'artbollocks-mode)

(defface artbollocks-passive-voice-face
  '((t (:foreground "Gray" :background "White")))
  "The face for passive voice words"
  :group 'artbollocks-mode)

(defface artbollocks-weasel-words-face
  '((t (:foreground "Brown" :background "White")))
  "The face for weasel-words words"
  :group 'artbollocks-mode)

(defface artbollocks-face
  '((t (:foreground "Purple" :background "White")))
  "The face for weasel-words words"
  :group 'artbollocks-mode)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lexical illusions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst artbollocks-lexical-illusions-regex "\\b\\(\\w+\\)\\W+\\(\\1\\)\\b")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Passive voice
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst artbollocks-passive-voice-regex "\\b\\(am\\|are\\|were\\|being\\|is\\|been\\|was\\|be\\)\\s-+\\(\\w+ed\\|awoken\\|been\\|born\\|beat\\|become\\|begun\\|bent\\|beset\\|bet\\|bid\\|bidden\\|bound\\|bitten\\|bled\\|blown\\|broken\\|bred\\|brought\\|broadcast\\|built\\|burnt\\|burst\\|bought\\|cast\\|caught\\|chosen\\|clung\\|come\\|cost\\|crept\\|cut\\|dealt\\|dug\\|dived\\|done\\|drawn\\|dreamt\\|driven\\|drunk\\|eaten\\|fallen\\|fed\\|felt\\|fought\\|found\\|fit\\|fled\\|flung\\|flown\\|forbidden\\|forgotten\\|foregone\\|forgiven\\|forsaken\\|frozen\\|gotten\\|given\\|gone\\|ground\\|grown\\|hung\\|heard\\|hidden\\|hit\\|held\\|hurt\\|kept\\|knelt\\|knit\\|known\\|laid\\|led\\|leapt\\|learnt\\|left\\|lent\\|let\\|lain\\|lighted\\|lost\\|made\\|meant\\|met\\|misspelt\\|mistaken\\|mown\\|overcome\\|overdone\\|overtaken\\|overthrown\\|paid\\|pled\\|proven\\|put\\|quit\\|read\\|rid\\|ridden\\|rung\\|risen\\|run\\|sawn\\|said\\|seen\\|sought\\|sold\\|sent\\|set\\|sewn\\|shaken\\|shaven\\|shorn\\|shed\\|shone\\|shod\\|shot\\|shown\\|shrunk\\|shut\\|sung\\|sunk\\|sat\\|slept\\|slain\\|slid\\|slung\\|slit\\|smitten\\|sown\\|spoken\\|sped\\|spent\\|spilt\\|spun\\|spit\\|split\\|spread\\|sprung\\|stood\\|stolen\\|stuck\\|stung\\|stunk\\|stridden\\|struck\\|strung\\|striven\\|sworn\\|swept\\|swollen\\|swum\\|swung\\|taken\\|taught\\|torn\\|told\\|thought\\|thrived\\|thrown\\|thrust\\|trodden\\|understood\\|upheld\\|upset\\|woken\\|worn\\|woven\\|wed\\|wept\\|wound\\|won\\|withheld\\|withstood\\|wrung\\|written\\)\\b")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Weasel words
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst artbollocks-weasel-words-regex "\\b\\(many\\|various\\|very\\|fairly\\|several\\|extremely\\|exceedingly\\|quite\\|remarkably\\|few\\|surprisingly\\|mostly\\|largely\\|huge\\|tiny\\|\\(\\(are\\|is\\) a number\\)\\|excellent\\|interestingly\\|significantly\\|substantially\\|clearly\\|vast\\|relatively\\|completely\\)\\b")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Artbollocks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst artbollocks-jargon-regex "\\b\\(a priori\\|ad hoc\\|affirmation\\|affirm\\|affirms\\|alterity\\|altermodern\\|aporia\\|aporetic\\|appropriates\\|appropriation\\|archetypal\\|archetypical\\|archetype\\|archetypes\\|autonomous\\|autonomy\\|baudrillardian\\|baudrillarian\\|commodification\\|committed\\|commitment\\|commonalities\\|contemporaneity\\|context\\|contexts\\|contextual\\|contextualise\\|contextualises\\|contextualisation\\|contextialize\\|contextializes\\|contextualization\\|contextuality\\|convention\\|conventional\\|conventions\\|coterminous\\|critique\\|cunning\\|cunningly\\|death of the author\\|debunk\\|debunked\\|debunking\\|debunks\\|deconstruct\\|deconstruction\\|deconstructs\\|deleuzian\\|desire\\|desires\\|dialectic\\|dialectical\\|dialectically\\|discourse\\|discursive\\|disrupt\\|disrupts\\|engage\\|engagement\\|engages\\|episteme\\|epistemic\\|ergo\\|fetish\\|fetishes\\|fetishise\\|fetishised\\|fetishize\\|fetishized\\|gaze\\|gender\\|gendered\\|historicise\\|historicisation\\|historicize\\|historicization\\|hegemonic\\|hegemony\\|identity\\|identity politics\\|intensifies\\|intensify\\|intensifying\\|interrogate\\|interrogates\\|interrogation\\|intertextual\\|intertextuality\\|irony\\|ironic\\|ironical\\|ironically\\|ironisation\\|ironization\\|ironises\\|ironizes\\|jouissance\\|juxtapose\\|juxtaposes\\|juxtaposition\\|lacanian\\|lack\\|loci\\|locus\\|locuses\\|matrix\\|mise en abyme\\|mocking\\|mockingly\\|modalities\\|modality\\|myth\\|mythologies\\|mythology\\|myths\\|narrative\\|narrativisation\\|narrativization\\|narrativity\\|nexus\\|nodal\\|node\\|normative\\|normativity\\|notion\\|notions\\|objective\\|objectivity\\|objectivities\\|objet petit a\\|ontology\\|ontological\\|operate\\|operates\\|otherness\\|othering\\|paradigm\\|paradigmatic\\|paradigms\\|parody\\|parodic\\|parodies\\|physicality\\|plenitude\\|poetics\\|popular notions\\|position\\|post hoc\\|post internet\\|post-internet\\|postmodernism\\|postmodernist\\|postmodernity\\|postmodern\\|practice\\|practise\\|praxis\\|problematic\\|problematics\\|problematise\\|problematize\\|proposition\\|qua\\|reading\\|readings\\|reification\\|relation\\|relational\\|relationality\\|relations\\|representation\\|representations\\|rhizomatic\\|rhizome\\|simulacra\\|simulacral\\|simulation\\|simulationism\\|simulationism\\|situate\\|situated\\|situates\\|stereotype\\|stereotypes\\|strategy\\|strategies\\|subjective\\|subjectivity\\|subjectivities\\|subvert\\|subversion\\|subverts\\|text\\|textual\\|textuality\\|thinker\\|thinkers\\|trajectory\\|transgress\\|transgresses\\|transgression\\|transgressive\\|unfolding\\|undermine\\|undermining\\|undermines\\|work\\|works\\|wry\\|wryly\\|zizekian\\|zižekian\\)\\b")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Highlighting
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun artbollocks-search-for-keyword (regex limit)
  "Match REGEX in buffer until LIMIT."
  (let (match-data-to-set
	found)
    (save-match-data
      (while (and (null match-data-to-set)
		  (re-search-forward regex limit t))
	    (setq match-data-to-set (match-data))))
    (when match-data-to-set
      (set-match-data match-data-to-set)
      (goto-char (match-end 0))
      t)))

(defun artbollocks-lexical-illusions-search-for-keyword (limit)
  (artbollocks-search-for-keyword artbollocks-lexical-illusions-regex limit))

(defun artbollocks-passive-voice-search-for-keyword (limit)
  (artbollocks-search-for-keyword artbollocks-passive-voice-regex limit))

(defun artbollocks-weasel-words-search-for-keyword (limit)
  (artbollocks-search-for-keyword artbollocks-weasel-words-regex limit))

(defun artbollocks-search-for-jargon (limit)
  (artbollocks-search-for-keyword artbollocks-jargon-regex limit))

(defconst artbollocks-lexicalkwlist
  '((artbollocks-lexical-illusions-search-for-keyword
     (2 'artbollocks-lexical-illusions-face t))))

(defconst artbollocks-passivekwlist
  '((artbollocks-passive-voice-search-for-keyword
     (0 'artbollocks-passive-voice-face t))))

(defconst artbollocks-weaselkwlist
  '((artbollocks-weasel-words-search-for-keyword
     (0 'artbollocks-weasel-words-face t))))

(defconst artbollocks-kwlist
  '((artbollocks-search-for-jargon
     (0 'artbollocks-face t))))

(defun artbollocks-add-keywords ()
  (when artbollocks-lexical-illusions
    (font-lock-add-keywords nil artbollocks-lexicalkwlist))
  (when artbollocks-passive-voice
    (font-lock-add-keywords nil artbollocks-passivekwlist))
  (when artbollocks-weasel-words
    (font-lock-add-keywords nil artbollocks-weaselkwlist))
  (when artbollocks-jargon
    (font-lock-add-keywords nil artbollocks-kwlist)))

(defun artbollocks-remove-keywords ()
  (font-lock-remove-keywords nil artbollocks-lexicalkwlist)
  (font-lock-remove-keywords nil artbollocks-passivekwlist)
  (font-lock-remove-keywords nil artbollocks-weaselkwlist)
  (font-lock-remove-keywords nil artbollocks-kwlist))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utility macros
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro interactive-optional-region ()
  "Flexible variation of (interactive \"r\").
Bind START and END parameters to either a selected region or the
entire buffer, subject to narrowing."
  `(interactive
    (if (use-region-p)
        (list (region-beginning) (region-end))
      (list (point-min) (point-max)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Text metrics
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun artbollocks-count-letters (&optional start end)
  (how-many "\\w" (or start (point-min)) (or end (point-max))))

(defun artbollocks-count-syllables (&optional start end)
  ;; Naively count vowel runs as syllable markers
  (how-many "[aeiouy]+" (or start (point-min)) (or end (point-max))))

(defun artbollocks-count-words (&optional start end)
  "Count the number of words between START and END."
  (interactive-optional-region)
  (let* ((s (or start (point-min)))
         (e (or end (point-max)))
         (result
          (if (fboundp 'count-words)
              (count-words s e)
            (how-many "\\w+" s e))))
    (if (called-interactively-p 'any)
        (message "Word count: %s" result))
    result))

(defun artbollocks-count-sentences (&optional start end)
  "Count the number of words between START and END."
  (interactive-optional-region)
  (let* ((s (or start (point-min)))
         (e (or end (point-max)))
         (result
          (how-many "\\w[!?.]" s e)))
    (if (called-interactively-p 'any)
        (message "Sentence count: %s" result))
    result))

(defun artbollocks-automated-readability-index (&optional start end)
  (let ((words (float (artbollocks-count-words start end)))
        (letters (float (artbollocks-count-letters start end)))
        (sentences (float (artbollocks-count-sentences start end))))
    (if (and (> words 0) (> sentences 0))
        (- (+ (* 4.71 (/ letters words))
              (* 0.5 (/ words sentences)))
           21.43)
      0.0)))

(defun artbollocks-flesch-reading-ease (&optional start end)
  (let ((words (float (artbollocks-count-words start end)))
        (sentences (float (artbollocks-count-sentences start end))))
    (if (and (> sentences 0) (> words 0))
        (- 206.834
           (* 1.015 (/ words sentences))
           (* 84.6 (/ syllables words)))
      0.0)))

(defun artbollocks-flesch-kinkaid-grade-level (&optional start end)
  (let ((words (float (artbollocks-count-words start end)))
        (sentences (float (artbollocks-count-sentences start end)))
        (syllables (float (artbollocks-count-syllables start end))))
    (if (and (> words 0) (> sentences 0))
        (- (+ (* 11.8 (/ syllables words))
              (* 0.39 (/ words sentences)))
           15.59)
      0.0)))

(defalias 'artbollocks-word-count 'artbollocks-count-words)
(defalias 'artbollocks-sentence-count 'artbollocks-count-sentences)

(defun artbollocks-readability-index (&optional start end)
  "Determine the automated readability index between START and END."
  (interactive-optional-region)
  (message "Readability index: %s" (artbollocks-automated-readability-index start end)))

(defun artbollocks-reading-ease (&optional start end)
  "Determine the Flesch reading ease between START and END."
  (interactive-optional-region)
  (message "Reading ease: %s" (artbollocks-flesch-reading-ease start end)))

(defun artbollocks-grade-level (&optional start end)
  "Determine the Flesch-Kinkaid grade level between START and END."
  (interactive-optional-region)
  (message "Grade level: %s" (artbollocks-flesch-kinkaid-grade-level start end)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The mode
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst artbollocks-mode-keymap (make-keymap))

(define-key artbollocks-mode-keymap (kbd "C-c [") 'artbollocks-word-count)
(define-key artbollocks-mode-keymap (kbd "C-c ]") 'artbollocks-sentence-count)
(define-key artbollocks-mode-keymap (kbd "C-c \\") 'artbollocks-readability-index)
(define-key artbollocks-mode-keymap (kbd "C-c /") 'artbollocks-reading-ease)
(define-key artbollocks-mode-keymap (kbd "C-c =") 'artbollocks-grade-level)

;;;###autoload
(define-minor-mode artbollocks-mode "Highlight passive voice, weasel words and artbollocks jargon in text, and provide useful text metrics"
  :lighter " AB"
  :keymap artbollocks-mode-keymap
  :group 'artbollocks-mode
  (if artbollocks-mode
      (artbollocks-add-keywords)
    (artbollocks-remove-keywords)))

(provide 'artbollocks-mode)

;; TODO
;; Toggle adding word/sentence count to status bar
;; Pluralization
;; Incorporate diction commands if available (and advise on installation if not)
;; Split general writing back out

;;; artbollocks-mode.el ends here
