;;; Here is the sort of configuration to use to add scratch into one's
;;; configuration if using el-get
;;; http://www.emacswiki.org/emacs/el-get.el

(setq el-get-sources
      (append 
       '(:name scratch
	       :type git
	       :url "git@github.com:cbbrowne/scratch-el.git"
	       :load-path "."
	       :info "."
	       :build ("make")
	       )
       el-get-sources))

;; You need now run (el-get) which pulls *all* modules including the
;; above, notably including pulling the Git repo.

(require 'scratch)