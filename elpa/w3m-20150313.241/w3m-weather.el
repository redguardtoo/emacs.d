;;; w3m-weather.el --- Look weather forecast -*- coding: iso-2022-7bit; -*-

;; Copyright (C) 2001, 2002, 2003, 2005, 2012
;; TSUCHIYA Masatoshi <tsuchiya@namazu.org>

;; Authors: TSUCHIYA Masatoshi <tsuchiya@namazu.org>
;; Keywords: w3m, WWW, hypermedia

;; This file is a part of emacs-w3m.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.


;;; Commentary:

;; w3m-weather.el is the add-on program of emacs-w3m to look weather
;; foracast.  For more detail about emacs-w3m, see:
;;
;;    http://emacs-w3m.namazu.org/


;;; How to install:

;; Please put this file to appropriate directory, and if you want
;; byte-compile it.  And add following lisp expressions to your
;; ~/.emacs.
;;
;;     (autoload 'w3m-weather "w3m-weather" "Display weather report." t)


;;; Code:

(eval-when-compile (require 'cl))
(require 'w3m)

(defconst w3m-weather-completion-table
  (eval-when-compile
    (let* ((format "http://weather.yahoo.co.jp/weather/jp/%s.html")
	   (alist
	    '(;; URL$B$N0lIt(B, $B4A;zI=5-(B, $B%m!<%^;zI=5-(B, $BJLL>(B
	      ;; ($B%m!<%^;zI=5-$G$OD92;$r>JN,$7$J$$$3$H(B)
	      ("1a/1100" "$BF;KL!&=!C+(B" "douhokusouya" "souya")
	      ("1a/1200" "$BF;KL!&>e@n(B" "douhokukamikawa" "kamikawa")
	      ("1a/1300" "$BF;KL!&N1K((B" "douhokurumoi" "rumoi")
	      ("1c/1710" "$BF;El!&LVAv(B" "doutouabashiri" "abashiri")
	      ("1c/1720" "$BF;El!&KL8+(B" "doutoukitami" "kitami")
	      ("1c/1730" "$BF;El!&LfJL(B" "doutoumonbetsu" "monbetsu")
	      ("1c/1800" "$BF;El!&:,<<(B" "doutounemuro" "nemuro")
	      ("1c/1900" "$BF;El!&6|O)(B" "doutoukushiro" "kushiro")
	      ("1c/2000" "$BF;El!&==>!(B" "doutoutokachi" "tokachi")
	      ("1b/1400" "$BF;1{!&@P<m(B" "dououishikari" "ishikari")
	      ("1b/1500" "$BF;1{!&6uCN(B" "douousorachi" "sorachi")
	      ("1b/1600" "$BF;1{!&8e;V(B" "dououshiribeshi" "shiribeshi")
	      ("1d/2400" "$BF;Fn!&I0;3(B" "dounanhiyama" "hiyama")
	      ("1d/2100" "$BF;Fn!&C@?6(B" "dounaniburi" "iburi")
	      ("1d/2200" "$BF;Fn!&F|9b(B" "dounanhidaka" "hidaka")
	      ("1d/2300" "$BF;Fn!&EOEg(B" "dounanoshima" "oshima")
	      ("1d/2400" "$BF;Fn!&[X;3(B" "dounanhiyama" "hiyama")
	      ("2/3110" "$B@D?98)!&DE7Z(B" "aomorikentsugaru" "tsugaru")
	      ("2/3120" "$B@D?98)!&2<KL(B" "aomorikenshimokita" "shimokita")
	      ("2/3130" "$B@D?98)!&;0H,>eKL(B"
	       "aomorikensanpachikamikita" "sanpachikamikita")
	      ("3/3310" "$B4d<j8)!&FbN&It(B" "iwatekennairikubu")
	      ("3/3320" "$B4d<j8)!&1h4_KLIt(B" "iwatekenenganhokubu")
	      ("3/3330" "$B4d<j8)!&1h4_FnIt(B" "iwatekenengannanbu")
	      ("5/3210" "$B=)ED8)!&1h4_It(B" "akitakenenganbu")
	      ("5/3220" "$B=)ED8)!&FbN&It(B" "akitakennairikubu")
	      ("4/3410" "$B5\>k8)!&ElIt(B" "miyagikentoubu")
	      ("4/3420" "$B5\>k8)!&@>It(B" "miyagikenseibu")
	      ("6/3510" "$B;37A8)!&B<;3(B" "yamagatakenmurayama" "murayama")
	      ("6/3520" "$B;37A8)!&CV;r(B" "yamagatakenokitama" "okitama")
	      ("6/3530" "$B;37A8)!&>1Fb(B" "yamagatakenshonai" "shounai")
	      ("6/3540" "$B;37A8)!&:G>e(B" "yamagatakenmogami" "mogami")
	      ("7/3610" "$BJ!Eg8)!&CfDL$j(B" "hukushimakennakadoori" "nakadoori")
	      ("7/3620" "$BJ!Eg8)!&IMDL$j(B" "hukushimakenhamadoori" "hamadoori")
	      ("7/3630" "$BJ!Eg8)!&2qDE(B" "hukushimakenaidu" "aidu")
	      ("8/4010" "$B0q>k8)!&KLIt(B" "ibaragikenhokubu")
	      ("8/4020" "$B0q>k8)!&FnIt(B" "ibaragikennanbu")
	      ("9/4110" "$BFJLZ8)!&FnIt(B" "tochigikennanbu")
	      ("9/4120" "$BFJLZ8)!&KLIt(B" "tochigikenhokubu")
	      ("10/4210" "$B72GO8)!&FnIt(B" "gunmakennanbu")
	      ("10/4220" "$B72GO8)!&KLIt(B" "gunmakenhokubu")
	      ("11/4310" "$B:k6L8)!&FnIt(B" "saitamakennanbu")
	      ("11/4320" "$B:k6L8)!&KLIt(B" "saitamakenhokubu")
	      ("11/4330" "$B:k6L8)!&CaIc(B" "saitamakenchichibu")
	      ("12/4510" "$B@iMU8)!&KL@>It(B" "chibakenhokuseibu")
	      ("12/4520" "$B@iMU8)!&KLElIt(B" "chibakenhokutoubu")
	      ("12/4530" "$B@iMU8)!&FnIt(B" "chibakennanbu")
	      ("13/4410" "$BEl5~ET!&El5~(B" "toukyoutotoukyou" "toukyou")
	      ("13/4420" "$BEl5~ET!&0KF&=tEgKLIt(B"
	       "toukyoutoizushotouhokubu" "izushotouhokubu")
	      ("13/100" "$BEl5~ET!&0KF&=tEgFnIt(B"
	       "toukyoutoizushotounanbu" "izushotounanbu")
	      ("13/9600" "$BEl5~ET!&>.3^86=tEg(B"
	       "toukyoutoogasawarashotou" "ogasawarashotou")
	      ("14/4610" "$B?@F`@n8)!&ElIt(B" "kanagawakentoubu")
	      ("14/4620" "$B?@F`@n8)!&@>It(B" "kanagawakenseibu")
	      ("15/5410" "$B?73c8)!&2<1[(B" "niigatakenkaetsu" "kaetsu")
	      ("15/5420" "$B?73c8)!&Cf1[(B" "niigatakenchuuetsu" "chuuetsu")
	      ("15/5430" "$B?73c8)!&>e1[(B" "niigatakenjouetsu" "jouetsu")
	      ("15/5440" "$B?73c8)!&:4EO(B" "niigatakensado" "sado")
	      ("16/5510" "$BIY;38)!&ElIt(B" "toyamakentoubu")
	      ("16/5520" "$BIY;38)!&@>It(B" "toyamakenseibu")
	      ("17/5610" "$B@P@n8)!&2C2l(B" "ishikawakenkaga" "kaga")
	      ("17/5620" "$B@P@n8)!&G=EP(B" "ishikawakennoto" "noto")
	      ("18/5710" "$BJ!0f8)!&NfKL(B" "hukuikenreihoku" "reihoku")
	      ("18/5720" "$BJ!0f8)!&NfFn(B" "hukuikenreinan" "reinan")
	      ("19/4910" "$B;3M|8)!&Cf@>It(B" "yamanashikenchuuseibu")
	      ("19/4920" "$B;3M|8)!&IY;N8^8P(B" "yamanashikenhujigoko" "hujigoko")
	      ("20/4810" "$BD9Ln8)!&KLIt(B" "naganokenhokubu")
	      ("20/4820" "$BD9Ln8)!&CfIt(B" "naganokenchuubu")
	      ("20/4830" "$BD9Ln8)!&FnIt(B" "naganokennanbu")
	      ("21/5210" "$B4tIl8)!&H~G;(B" "gihukenmino" "mino")
	      ("21/5220" "$B4tIl8)!&HtBM(B" "gihukenhida" "hida")
	      ("22/5010" "$B@E2,8)!&CfIt(B" "shizuokakenchuubu")
	      ("22/5020" "$B@E2,8)!&0KF&(B" "shizuokakenizu" "izu")
	      ("22/5030" "$B@E2,8)!&ElIt(B" "shizuokakentoubu")
	      ("22/5040" "$B@E2,8)!&@>It(B" "shizuokakenseibu")
	      ("23/5110" "$B0&CN8)!&@>It(B" "aichikenseibu")
	      ("23/5120" "$B0&CN8)!&ElIt(B" "aichikentoubu")
	      ("24/5310" "$B;0=E8)!&KLCfIt(B" "miekenhokuchuubu")
	      ("24/5320" "$B;0=E8)!&FnIt(B" "miekennanbu")
	      ("25/6010" "$B<"2l8)!&FnIt(B" "shigakennanbu")
	      ("25/6020" "$B<"2l8)!&KLIt(B" "shigakenhokubu")
	      ("26/400" "$B5~ETI\!&KLIt(B" "kyoutohuhokubu")
	      ("26/6100" "$B5~ETI\!&FnIt(B" "kyoutohunanbu")
	      ("27/6200" "$BBg:eI\(B" "oosakahu" "oosaka")
	      ("28/500" "$BJ<8K8)!&KLIt(B" "hyougokenhokubu")
	      ("28/6300" "$BJ<8K8)!&FnIt(B" "hyougokennanbu")
	      ("29/6410" "$BF`NI8)!&KLIt(B" "narakenhokubu")
	      ("29/6420" "$BF`NI8)!&FnIt(B" "narakennanbu")
	      ("30/6510" "$BOB2N;38)!&KLIt(B" "wakayamakenhokubu")
	      ("30/6520" "$BOB2N;38)!&FnIt(B" "wakayamakennanbu")
	      ("31/6910" "$BD;<h8)!&ElIt(B" "tottorikentoubu")
	      ("31/6920" "$BD;<h8)!&@>It(B" "tottorikenseibu")
	      ("32/600" "$BEg:,8)!&1#4t(B" "shimanekenoki" "oki")
	      ("32/6810" "$BEg:,8)!&ElIt(B" "shimanekentoubu")
	      ("32/6820" "$BEg:,8)!&@>It(B" "shimanekenseibu")
	      ("33/6610" "$B2,;38)!&FnIt(B" "okayamakennanbu")
	      ("33/6620" "$B2,;38)!&KLIt(B" "okayamakenhokubu")
	      ("34/6710" "$B9-Eg8)!&FnIt(B" "hiroshimakennanbu")
	      ("34/6720" "$B9-Eg8)!&KLIt(B" "hiroshimakenhokubu")
	      ("35/8110" "$B;38}8)!&@>It(B" "yamaguchikenseibu")
	      ("35/8120" "$B;38}8)!&CfIt(B" "yamaguchikenchuubu")
	      ("35/8140" "$B;38}8)!&KLIt(B" "yamaguchikenhokubu")
	      ("35/8130" "$B;38}8)!&ElIt(B" "yamaguchikentoubu")
	      ("36/7110" "$BFAEg8)!&KLIt(B" "tokushimakenhokubu")
	      ("36/7120" "$BFAEg8)!&FnIt(B" "tokushimakennanbu")
	      ("37/7200" "$B9a@n8)(B" "kagawaken" "kagawa")
	      ("38/7320" "$B0&I28)!&ElM=(B" "ehimekentouyo" "touyo")
	      ("38/7330" "$B0&I28)!&FnM=(B" "ehimekennanyo" "nanyo")
	      ("38/7310" "$B0&I28)!&CfM=(B" "ehimekenchuuyo" "chuuyo")
	      ("39/7410" "$B9bCN8)!&CfIt(B" "kouchikenchuubu")
	      ("39/7420" "$B9bCN8)!&ElIt(B" "kouchikentoubu")
	      ("39/7430" "$B9bCN8)!&@>It(B" "kouchikenseibu")
	      ("40/8210" "$BJ!2,8)!&J!2,(B" "hukuokakenhukuoka" "hukuoka")
	      ("40/8220" "$BJ!2,8)!&KL6e=#(B" "hukuokakenkitakyushu" "kitakyuushu")
	      ("40/8230" "$BJ!2,8)!&C^K-(B" "hukuokakenchikuhou" "chikuhou")
	      ("40/8240" "$BJ!2,8)!&C^8e(B" "hukuokakenchikugo" "chikugo")
	      ("41/8510" "$B:42l8)!&FnIt(B" "sagakennanbu")
	      ("41/8520" "$B:42l8)!&KLIt(B" "sagakenhokubu")
	      ("42/700" "$BD9:j8)!&0m4tBPGO(B"
	       "nagasakikenikitsushima" "iki" "tsushima" "ikitsushima")
	      ("42/800" "$BD9:j8)!&8^Eg(B" "nagasakikengotou" "gotou")
	      ("42/8410" "$BD9:j8)!&FnIt(B" "nagasakikennanbu")
	      ("42/8420" "$BD9:j8)!&KLIt(B" "nagasakikenhokubu")
	      ("43/8610" "$B7'K\8)!&7'K\(B" "kumamotokenkumamoto" "kumamoto")
	      ("43/8620" "$B7'K\8)!&0$AI(B" "kumamotokenaso" "aso")
	      ("43/8630" "$B7'K\8)!&E7Ap02KL(B"
	       "kumamotokenamakusaashikita" "amakusa" "ashikita" "amakusaashikita")
	      ("43/8640" "$B7'K\8)!&5eKa(B" "kumamotokenkuma" "kuma")
	      ("44/8310" "$BBgJ,8)!&CfIt(B" "ooitakenchuubu")
	      ("44/8320" "$BBgJ,8)!&KLIt(B" "ooitakenhokubu")
	      ("44/8330" "$BBgJ,8)!&@>It(B" "ooitakenseibu")
	      ("44/8340" "$BBgJ,8)!&FnIt(B" "ooitakennanbu")
	      ("45/8710" "$B5\:j8)!&FnItJ?LnIt(B" "miyazakikennanbuheiyabu")
	      ("45/8720" "$B5\:j8)!&KLItJ?LnIt(B" "miyazakikenhokubuheiyabu")
	      ("45/8730" "$B5\:j8)!&FnIt;31h$$(B" "miyazakikennanbuyamazoi")
	      ("45/8740" "$B5\:j8)!&KLIt;31h$$(B" "miyazakikenhokubuyamazoi")
	      ("46/8810" "$B</;yEg8)!&;'K`(B" "kagoshimakensatsuma" "satsuma")
	      ("46/8820" "$B</;yEg8)!&Bg6y(B" "kagoshimakenoosumi" "oosumi")
	      ("46/900" "$B</;yEg8)!&<o;REg!&205WEg(B"
	       "kagoshimakentanegashimayakushima" "tanegashima" "yakushima" "tanegashimayakushima")
	      ("46/1000" "$B</;yEg8)!&1bH~(B" "kagoshimakenamami" "amami")
	      ("47/9110" "$B2-Fl8)!&K\EgCfFnIt(B"
	       "okinawakenhontouchuunanbu" "hontouchuunanbu")
	      ("47/9120" "$B2-Fl8)!&K\EgKLIt(B"
	       "okinawakenhontouhokubu" "hontouhokubu")
	      ("47/9130" "$B2-Fl8)!&5WJFEg(B" "okinawakenkumejima" "kumejima")
	      ("47/9200" "$B2-Fl8)!&BgElEg(B" "okinawakendaitoujima" "daitoujima")
	      ("47/9300" "$B2-Fl8)!&5\8EEg(B" "okinawakenmiyakojima" "miyakojima")
	      ("47/9400" "$B2-Fl8)!&@P3@Eg(B"
	       "okinawakenishigakijima" "ishigakijima")
	      ("47/9500" "$B2-Fl8)!&M?Fa9qEg(B"
	       "okinawakenyonagunijima" "yonagunijima")))
	   (table)
	   ;; $B%X%\%s<0$H71Na<0$NBP1~I=(B
	   (hepburn-table
	    (let (table)
	      (dolist (x '(("si" "shi")
			   ("zi" "ji")
			   ("zu" "du")
			   ("ti" "chi")
			   ("tu" "tsu")
			   ("hu" "fu")))
		(push x table)
		(push (reverse x)table))
	      (dolist (x '(("sy" . "sh")
			   ("zy" . "j")
			   ("ty" . "ch")))
		(dolist (y '("a" "u" "o"))
		  (push (list (concat (car x) y) (concat (cdr x) y)) table)
		  (push (list (concat (cdr x) y) (concat (car x) y)) table)))
	      table))
	   ;; $BBP1~I=$K>h$C$F$$$kJ8;zNs$rC5$9@55,I=8=(B
	   (hepburn-regexp
	    (format "\\(?:\\`\\|[aiueo]\\)\\(n\\([^aiueoy]\\)\\|%s\\)"
		    (regexp-opt (mapcar (function car) hepburn-table))))
	   ;; $BD92;$NM-L5$K$h$kGI@87A$NI=(B
	   (prolonged-table
	    (let (table)
	      (dolist (x '("k" "ky"
			   "s" "sy" "sh"
			   "t" "ty" "ch"
			   "n" "ny"
			   "h" "hy"
			   "m" "my"
			   "y"
			   "r" "ry"
			   "w"
			   "g" "gy"
			   "z" "zy" "j"
			   "d" "dy"
			   "b" "by"
			   "p" "py"))
		(let ((long-vowels '("ou" "oo" "o-")))
		  (dolist (y long-vowels)
		    (push (cons (concat x y)
				(append
				 (mapcar
				  (lambda (z) (concat x z))
				  (delete y (copy-sequence long-vowels)))
				 (list (concat x "o"))))
			  table)))
		(push (list (concat x "uu") (concat x "u"))
		      table))
	      table))
	   ;; $BGI@87A$NI=$K>h$C$F$$$kJ8;zNs$rC5$9@55,I=8=(B
	   (prolonged-regexp (format "\\(?:\\`\\|[aiueo]\\)\\(%s\\)"
				     (regexp-opt (mapcar (function car)
							 prolonged-table)))))
      (w3m-labels ((hepburn-candidates
		    (str)
		    "$B%X%\%s<0$H71Na<0$N:9$K$h$C$F@8$8$kGI@87A$rF@$k(B"
		    (if (string-match hepburn-regexp str)
			(let ((prefix (substring str 0 (match-beginning 1)))
			      (candidates (if (match-beginning 2)
					      '("n" "nn")
					    (assoc (match-string 1 str)
						   hepburn-table)))
			      (suffixes
			       (hepburn-candidates
				(substring str (or (match-beginning 2)
						   (match-end 0)))))
			      (buf))
			  (dolist (x candidates)
			    (dolist (y suffixes)
			      (push (concat prefix x y) buf)))
			  buf)
		      (list str)))
		   (prolonged-candidates
		    (str)
		    "$BD92;$NM-L5$K$h$C$F@8$8$kGI@87A$rF@$k(B"
		    (let (buf)
		      (if (string-match prolonged-regexp str)
			  (let ((prefix (substring str 0 (match-beginning 1)))
				(candidates (assoc (match-string 1 str)
						   prolonged-table))
				(suffixes (prolonged-candidates
					   (substring str (match-end 0)))))
			    (dolist (x candidates)
			      (dolist (y suffixes)
				(push (concat prefix x y) buf))))
			(setq buf (list str)))
		      (dolist (x buf)
			(when (string-match "\\(\\`\\|[aiue]\\)oo" x)
			  (let ((prefix (substring x 0 (match-end 1)))
				(suffix (substring x (match-end 0))))
			    (dolist (y '("o" "oh" "o-"))
			      (push (concat prefix y suffix) buf)))))
		      buf))
		   (romaji-candidates
		    (str)
		    "$BA4$F$NGI@87A$rF@$k(B"
		    (let (buf)
		      (dolist (x (hepburn-candidates str))
			(dolist (y (prolonged-candidates x))
			  (push y buf)))
		      buf)))
	(dolist (area alist)
	  (let ((url (format format (car area)))
		(kanji (cadr area)))
	    (push (list kanji (nth 2 area) url) table)
	    (dolist (romaji (cddr area))
	      (dolist (x (romaji-candidates romaji))
		(push (list x kanji) table)))))
	(nreverse table))))
  "Completion table of areas and urls.")

(defcustom w3m-weather-default-area
  "$B5~ETI\!&FnIt(B"
  "Default region to check weather."
  :group 'w3m
  :type (cons 'radio
	      (delq nil
		    (mapcar (lambda (area)
			      (when (nth 2 area)
				(list 'const (car area))))
			    w3m-weather-completion-table))))

(defcustom w3m-weather-filter-functions
  '(w3m-weather-extract-contents
    w3m-weather-adjust-contents
    w3m-weather-expand-anchors
    w3m-weather-insert-title)
  "Filter functions to remove useless tags."
  :group 'w3m
  :type 'hook)

(defvar w3m-weather-input-history nil)

(defun w3m-weather-input-area ()
  (let* ((str
	  (completing-read (format "Input area (default %s): "
				   w3m-weather-default-area)
			   'w3m-weather-area-completion nil t nil
			   'w3m-weather-input-history))
	 (area
	  (cond
	   ((string= "" str) w3m-weather-default-area)
	   ((string-match "[^-a-zA-Z]" str) str)
	   (t (cadr (assoc str w3m-weather-completion-table))))))
    (setq w3m-weather-input-history
	  (cons area
		(delete area
			(delete str w3m-weather-input-history))))
    area))

(defun w3m-weather-area-completion (partial predicate flag)
  (if (eq flag 'lambda)
      (and (assoc partial w3m-weather-completion-table)
	   (or (not predicate)
	       (funcall predicate partial))
	   t)
    (let ((kanji "")
	  (romaji "")
	  (romaji-partial partial))
      (when (string-match "\\`\\(?:[^-a-zA-Z]+\\)" partial)
	(let ((suffix (substring partial (match-end 0))))
	  (setq kanji (substring partial 0 (match-end 0))
		romaji (try-completion
			""
			(mapcar
			 (lambda (x)
			   (list (cadr (assoc x w3m-weather-completion-table))))
			 (all-completions kanji w3m-weather-completion-table)))
		romaji-partial (concat romaji suffix))))
      (let ((collection)
	    (regexp
	     (and (string-match "$B!&(B\\'" kanji)
		  (string-match "[aiueo]n\\'" romaji)
		  (concat "\\`" romaji "n[^aiueoy]"))))
	(dolist (x (all-completions romaji-partial w3m-weather-completion-table))
	  (unless (and regexp (string-match regexp x))
	    (setq x (assoc x w3m-weather-completion-table))
	    (unless (assoc (cadr x) collection)
	      (push (cons (cadr x) (car x)) collection))))
	(cond
	 ((not flag)
	  (let ((s (try-completion kanji collection predicate)))
	    (if (and (stringp s) (string< s partial))
		(when (setq s (try-completion romaji-partial
					      (mapcar (lambda (x) (list (cdr x)))
						      collection)
					      predicate))
		  (concat kanji (substring s (if romaji (length romaji) 0))))
	      s)))
	 ((eq flag t)
	  (all-completions kanji collection predicate)))))))

;;;###autoload
(defun w3m-weather (area)
  "Display weather report."
  (interactive
   (list (if current-prefix-arg
	     (w3m-weather-input-area)
	   w3m-weather-default-area)))
  (w3m-goto-url (format "about://weather/%s" area)))

;;;###autoload
(defun w3m-about-weather (url no-decode no-cache post-data referer handler)
  (if (string-match "\\`about://weather/" url)
      (lexical-let* ((url url)
		     (no-cache no-cache)
		     (area (substring url (match-end 0)))
		     (furl (nth 2 (assoc area w3m-weather-completion-table))))
	(w3m-process-do
	    (type (w3m-retrieve furl nil no-cache nil nil handler))
	  (when type
	    (w3m-decode-buffer furl)
	    (w3m-weather-run-filter-functions w3m-weather-filter-functions
					      area furl no-cache handler))))
    (w3m-message "Unknown URL: %s" url)
    nil))

(defun w3m-weather-run-filter-functions (functions area url no-cache handler)
  (if functions
      (lexical-let ((functions functions)
		    (area area)
		    (url url)
		    (no-cache no-cache))
	(w3m-process-do
	    (nil (funcall (pop functions) area url no-cache handler))
	  (w3m-weather-run-filter-functions functions area url
					    no-cache handler)))
    "text/html"))

(defun w3m-weather-extract-contents (&rest args)
  "Remove both header and footer in the weather forecast pages."
  (goto-char (point-min))
  (when (search-forward "<!---MAIN_CONTENTS_table--->" nil t)
    (delete-region (point-min) (match-beginning 0)))
  (goto-char (point-max))
  (when (search-backward "<!---Local_Link--->" nil t)
    (delete-region (match-beginning 0) (point-max))))

(defun w3m-weather-adjust-contents (&rest args)
  ;; Remove spacers.
  (goto-char (point-min))
  (while (search-forward "<tr><td>\
<img src=\"http://img.yahoo.co.jp/images/clear.gif\" width=1>\
</td></tr>" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  ;; Remove execessive tables.
  (goto-char (point-min))
  (while (re-search-forward "<table[^>]*>[ \t\r\f\n]*</table>" nil t)
    (delete-region (match-beginning 0) (match-end 0)))
  (goto-char (point-min))
  ;; Remove too narrow width parameters.
  (while (re-search-forward "<td[^>]*\\(width=1%\\)" nil t)
    (delete-region (match-beginning 1) (match-end 1)))
  ;; Display border lines.
  (goto-char (point-min))
  (while (re-search-forward "\
<table border=\\(0\\) cellpadding=[1-9][0-9]* cellspacing=[1-9][0-9]*" nil t)
    (goto-char (match-beginning 1))
    (delete-char 1)
    (insert "1"))
  (goto-char (point-min))
  (while (re-search-forward
	  "<td align=center width=25%>[ \t\r\f\n]*<table border=1" nil t)
    (delete-char -1)
    (insert "0")))

(defun w3m-weather-insert-title (area url &rest args)
  "Insert title."
  (goto-char (point-min))
  (insert "<head><title>Weather forecast of "
	  area
	  "</title></head>\n"
	  "<body><p align=left><a href=\""
	  url
	  "\">[Yahoo!]</a></p>\n")
  (goto-char (point-max))
  (insert "</body>"))

(defun w3m-weather-expand-anchors (area url &rest args)
  ;; FIXME: $BE75$M=Js%Z!<%8$K4^$^$l$F$$$kAjBP%j%s%/$r@dBP%j%s%/$K=q$-49(B
  ;; $B$($k$?$a$N4X?t!%$3$l$i$NAjBP%j%s%/$r0BA4$K<h$j07$&$?$a$K$O!$(Bbase
  ;; URL $B$rJV$;$k$h$&$K!$(Babout:// $B$N9=B$$r=q$-D>$9I,MW$,$"$k$H9M$($i$l(B
  ;; $B$k$,!$$H$j$"$($:8e2s$7!%(B
  (goto-char (point-min))
  (while (re-search-forward
	  (eval-when-compile
	    (concat "<a[ \t\r\f\n]+href=" w3m-html-string-regexp))
	  nil t)
    (replace-match (format
		    "<a href=\"%s\""
		    (w3m-expand-url (w3m-remove-redundant-spaces
				     (or (match-string-no-properties 2)
					 (match-string-no-properties 3)
					 (match-string-no-properties 1)))
				    url)))))

(provide 'w3m-weather)

;;; w3m-weather.el ends here.
