;;; evil-matchit-verilog.el ---verilog plugin of evil-matchit

;; Copyright (C) 2014-2016 Chen Bin <chenbin.sh@gmail.com>

;; Author: Chen Bin <chenbin.sh@gmail.com>

;; This file is not part of GNU Emacs.

;;; License:

;; This file is part of evil-matchit
;;
;; evil-matchit is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; evil-matchit is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Code:

;; OPTIONAL, you don't need SDK to write a plugin for evil-matchit
;; but SDK don make you write less code, isn't it?
;; All you need to do is just define the match-tags for SDK algorithm to lookup.
(require 'evil-matchit-sdk)

;; {{ Sample verilog code:
;; module dff_lab;
;;    reg data,rst;
;;    // Connecting ports by name.(map)
;;    dff d1 (.qb(outb), .q(out),
;;            .clk(clk),.d(data),.rst(rst));
;;    // overriding module parameters
;;    defparam
;;      dff_lab.dff.n1.delay1 = 5 ,
;;      dff_lab.dff.n2.delay2 = 6 ;
;;    // full-path referencing is used
;;    // over-riding by using #(8,9) delay1=8..
;;    dff d2 #(8,9) (outc, outd, clk, outb, rst);
;;    // clock generator
;;    always clk = #10 ~clk ;
;;    // stimulus ... contd
;;    initial begin: stimuli // named block stimulus
;;       clk = 1; data = 1; rst = 0;
;;       #20 rst = 1;
;;       #20 data = 0;
;;       #600 $finish;
;;    end
;;    initial // hierarchy: downward path referencing
;;      begin
;;         #100 force dff.n2.rst = 0 ;
;;         #200 release dff.n2.rst;
;;      end
;; endmodule
;; }}

;; should try next howto, the purpose is avoid missing any howto
(defvar evilmi-verilog-extract-keyword-howtos
  '(("^[ \t]*\\(while\\|module\\|primitive\\|case\\|function\\|specify\\|table\\|class\\|program\\|clocking\\|property\\|sequence\\|package\\covergroup\\|generate\\|interface\\|task\\|fork\\|join[a-z]*\\)" 1)
    ("^[ \t]*\\(end[a-z]+\\)" 1)
    ("^[ \t]*\\(`[a-z]+\\)" 1) ; macro
    ("\\([^a-z]\\|^\\)\\(begin\\|end\\)\\([^a-z]\\|$\\)" 2)))

(defvar evilmi-verilog-match-tags
  '(("module" () "endmodule" "MONOGAMY")
    ("primitive" () "endprimitive" "MONOGAMY")
    ("case" () "endcase" "MONOGAMY")
    ("function" () "endfunction" "MONOGAMY")
    ("specify" () "endspecify" "MONOGAMY")
    ("table" () "endtable" "MONOGAMY")
    ("class" () "endclass" "MONOGAMY")
    ("program" () "endprogram" "MONOGAMY")
    ("clocking" () "endclocking" "MONOGAMY")
    ("property" () "endproperty" "MONOGAMY")
    ("sequence" () "endsequence" "MONOGAMY")
    ("package" () "endpackage" "MONOGAMY")
    ("covergroup" () "endgroup" "MONOGAMY")
    ("generate" () "endgenerate" "MONOGAMY")
    ("interface" () "endinterface" "MONOGAMY")
    ("task" () "endtask" "MONOGAMY")
    ("fork" () ("join" "join_any" "join_none") "MONOGAMY")
    ("begin" () "end")
    ("`ifn?def" "`else" "`endif" "MONOGAMY")
    ("`celldefine" () "`endcelldefine" "MONOGAMY")
    ))

;;;###autoload
(defun evilmi-verilog-get-tag ()
  (let* ((orig-info (evilmi-sdk-get-tag evilmi-verilog-match-tags
                                        evilmi-verilog-extract-keyword-howtos)))
    (if evilmi-debug (message "evilmi-verilog-get-tag called => %s" orig-info))
    ;; hack if current line is `if' or `else if'
    (unless orig-info
      (let* ((cur-line (evilmi-sdk-curline))
             next-line
             (pos (line-beginning-position)))
        (when (string-match "^[ \t]*\\(if\\(n?def\\)?\\|else\\( if\\)?\\).*" cur-line)
          ;; second chance for if else statement
          (save-excursion
            (forward-line 1)
            (setq orig-info (evilmi-sdk-get-tag evilmi-verilog-match-tags
                                                evilmi-verilog-extract-keyword-howtos)))
          ;; move to the next line now. maybe there exist end statement
          (when orig-info
            (forward-line 1)
            (setq orig-info (cons pos (cdr orig-info)))))))
    orig-info))

;;;###autoload
(defun evilmi-verilog-jump (orig-info num)
  (let* ((orig-keyword (evilmi-sdk-keyword (cadr orig-info))))
    (if evilmi-debug (message "evilmi-verilog-jump called => %s" orig-info))
    (evilmi-sdk-jump orig-info
                     num
                     evilmi-verilog-match-tags
                     evilmi-verilog-extract-keyword-howtos)))

(provide 'evil-matchit-verilog)
;;; evil-matchit-verilog.el ends here