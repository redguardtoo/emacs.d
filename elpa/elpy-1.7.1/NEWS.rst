New in Elpy 1.7.1
=================

- Do not fail on errors from importmagic.
- Handle new minor mode behavior of new versions of yasnippet.
- Do use the argument to ``elpy-use-ipython`` correctly.
- Handle unexpected data from the backend more gracefully.


New in Elpy 1.7.0
=================

- Elpy now can add missing import directives automatically, by using
  Alec Thomas' excellent importmagic_ library. Use ``C-c C-m`` to add
  a single import statement, or ``C-c C-S-m`` to include all missing
  import statements. Many thanks to Georg Brandl for doing a lot of
  work to bring this feature to Elpy!
- The Jedi backend now also supports ``C-c C-d`` to display a
  docstring. Thanks again to Georg Brandl for the patch.
- It is now possible to disable the display of the current function in
  the echo area by setting ``elpy-eldoc-show-current-function`` to
  ``nil``.
- idomenu was removed.
- Twisted's Trial test runner is now supported. Thanks to Elric Milon
  for the patch!
- All test runners now use a variable to decide which command to run,
  which for example allows using ``manage.py`` for the Django test
  runner, or your own test script which sets up the environment
  correctly.
- Emacs 24.4 is now officially supported.
- Various bugfixes.

.. _importmagic: https://github.com/alecthomas/importmagic

New in Elpy 1.6.0
=================

- When point is on a line with a flymake error, Elpy will now show the
  error in the echo area.
- The movement commands (``C-<cursor>``) have been reworked again.
  Going left and right will now move by indentation levels left of the
  current indentation, i.e. jump four spaces, and by words right of
  the current indentation. Going up and down will go to the previous
  or next line with the indentation level point is at, not the
  indentation the line has. Try it, it's more difficult to explain
  than to use.
- Completion results are now sorted more sensibly, with
  single-underscore symbols at the end, and double-underscore symbols
  after normal symbols, but before single-underscore ones.
- ``M-x elpy-config`` will now point out if there are newer versions
  available for packages used by Elpy.
- ``M-x elpy-config`` will now warn if ``~/.local/bin`` is not in
  ``PATH`` while there is no virtualenv active.
- The ``M-x elpy-version`` command is back by popular demand.
- RPC buffers used by Elpy are now hidden by default, having a space
  at the beginning of the name.
- When the Rope library throws an error, Elpy will now also attempt to
  provide reproduction steps. This used to only happen for Jedi.
- Various bug fixes.


New in Elpy 1.5.1
=================

- Fix a bug where company-mode might get confused about the current
  backend, leading to an error about ``Symbol's function definition is
  void: nil``
- Fix Rope so it won’t search the whole project directory. This was an
  intended feature in v1.5 which did not work originally.
- Use ``yas-text`` instead of ``text`` in snippets for compatibility
  with the unreleased yasnippet from MELPA (thanks to Daniel Wu!)

New in Elpy 1.5.0
=================

- Elpy now has a `manual`_. Additionally, there's a menu bar now which
  should make it easier to discover Elpy features.
- The Elpy Python package now ships with the Emacs Lisp package,
  removing the need to install Elpy via pip.
- Python 3.4 is now officially supported.
- The new command ``elpy-config`` can be used to configure Elpy using
  Emacs' built-in customize system. Elpy has been changed to make the
  most of this.
- Elpy now uses company-mode instead of auto-complete for on-the-fly
  auto completion. This changes a few things. There is no automatic
  documentation popup anymore. Instead, you can type ``C-d`` and get
  the documentation buffer. In addition, you can type ``C-w`` to see
  the source of the current candidate in context.
- Elpy now uses pyvenv as the virtualenv module, enabling
  virtualenvwrapper hooks.
- We now ship with a large number of YASnippet snippets. Try ``M-x
  yas-insert-snippet``.
- The new unified test running interface on ``C-c C-t`` will try to
  determine the current test and run it, or, failing that, run all
  tests. Provide a prefix argument to just run all tests no matter
  what. You can change the test runner to be used using
  ``elpy-set-test-runner``. Elpy supports the default unittest
  discover runner, the Django discover runner, nosetests and py.test
  by default. New test runners can easily be defined.
- There's a new multi-edit functionality. ``C-c C-e`` will edit all
  occurrences of the symbol under point. When using Jedi, this is
  using semantic information as opposed to just syntactic one. When a
  region is active, edit all occurrences of the text in region in the
  current buffer.
- When sending Python code to the interactive interpreter using ``C-c
  C-c``, Elpy will now not automatically pop to the interpreter
  anymore. Use ``C-c C-z`` to switch to the interpreter.
- Elpy will now display the current class and function if there is no
  call tip to be displayed. Removes the ``C-c C-q`` binding.
- If there is a call tip, highlight the current argument (requires Jedi).
- The documentation interface using ``C-c C-d`` is much smarter now,
  falling back to pydoc when necessary and providing sensible
  completion for that, too. Provide a prefix argument if you want no
  smarts, just pydoc.
- ``<S-return>`` and ``<C-S-return>`` now open a line below or above
  the current one.
- ``<C-cursor>`` will now navigate between Python blocks of the same
  indentation level. ``<M-cursor>`` will move the current block. Try
  it, it's easier to understand when you see it than to explain it.
- There's a new concept of modules. The variable
  ``elpy-default-minor-modes`` is gone (use ``elpy-mode-hook`` for
  minor modes). Instead, there's now ``elpy-modules`` which can be
  used to enable or disable certain features of Elpy.
- ``elpy-clean-modeline`` is gone, modules now clean themselves up.
- Elpy now distinguishes between the project root, where project files
  are located, and the library root, which should be part of
  ``sys.path`` to import the module under development.
- ``elpy-project-ignored-directories`` replaces the old
  ``elpy-rgrep-ignored-directories`` and is used by more features.
- ``elpy-doc-websearch`` has been removed as it was barely useable
  as is.
- Elpy now tries to be more helpful when errors in the backend happen.
  This removes ``elpy-rpc-traceback``, as that will be displayed by
  default.
- Optimizations were added to handle large files, making general
  interaction a lot faster.
- When Rope is being used, do not search through unusually large
  directories. This should speed up interaction in those cases,
  especially when editing a file in the home directory.
- And a whole lot of minor bug fixes and little improvements.

.. _manual: http://elpy.readthedocs.org/


New in Elpy 1.4.2
==================

- Minor bugfix to prevent an error from projectile-project-root to
  interfere with Elpy’s project finding strategy.

New in Elpy 1.4.1
=================

- Elpy now sets project-wide preferences for Rope, enabling completion
  in the sys package, among others.
- An error is avoided in the Jedi backend when trying to go to symbols
  in compiled packages.
- A compatibility alias was added for nose.el, which insists on
  breaking backwards compatibility with Emacs 24.x.

New in Elpy 1.4.0
=================

- Elpy has moved to its own ELPA. Make sure to update your
  package-archives (as described above).
- For a file in a Projectile-managed project is opened, Elpy will now
  use Projectile’s project root.
- When the user has set a valid python-check-command, elpy will now
  refrain from overriding it.
- On Windows, elpy is now using the pythonw.exe interpreter for the
  RPC process, as that seems to be causing fewer issues.
- And various smaller bugfixes.

New in Elpy 1.3.0
=================

- virtualenv.el has been replaced by pyvenv.el, as that library offers
  more features.
- elpy-rpc-restart now works globally, not just in Elpy buffers.
- Elpy does not try to complete in comments anymore.
- The new command elpy-rpc-traceback gives access to the last stack
  trace in the Elpy backend, helping with debugging problems.
- The flymake check function is now run with the current directory as
  / to avoid accidental imports.
- Ensure correct handling of yas-snippet-dirs by Elpy. This variable
  can be a string, so ensure it’s a list before adding to it.
- The new variable elpy-show-installation-instructions can be used to
  disable the installation screen.
- Fix a very nasty bug causing spurious empty lines in a buffer or
  consume 100% CPU in certain situations when using the Jedi backend.
  Thanks to Matthias Dahl for finding this bug.
- Various other bugfixes.

New in Elpy 1.2.1
=================

Bugfix release.

- The refactoring was not ported to the new asynchronous API,
  resulting in an error when refactoring was attempted.
- The project root now always returns a directory. Too many parts of
  elpy relies on this. If the project root turns out to be your home
  directory, elpy will warn you about it.
- Elpy now works correctly with Emacs 24.2. There were some
  compatibility functions missing.
- Blocking RPC calls now do not block for one second even if there is
  process output.

New in Elpy 1.2
===============

- Elpy now uses asynchronous RPC. This means that Emacs should not
  freeze anymore while eldoc or auto-complete functions run.
- ``elpy-shell-send-region-or-buffer`` will now remove common
  indentation of the region, making it possible to easily send parts
  of an if statement or function body without manually adjusting the
  indentation.
- The Python package depends on ``flake8``, and will also try to be
  smarter when detecting ``flake8`` for on-the-fly checking.
- ``elpy-check`` can be run with a prefix argument to check the whole
  project, instead of only the current file.
- ``elpy-rgrep-symbol`` now ignores a few common directories
  (``.tox``, ``build``, ``dist``).
- When using the rope backend, Elpy will not create the
  ``.ropeproject`` folders anymore. This should keep projects a lot
  cleaner.

New in Elpy 1.1
===============

- Elpy now always uses the root directory of the package as the
  project root; this should avoid some confusion and improve
  auto-completion suggestions
- ``elpy-shell-send-region-or-buffer`` now accepts a prefix argument
  to run code wrapped behind ``if __name__ == '__main__'``, which is
  ignored by default
- ``elpy-project-root`` is now a safe local variable and can be set
  from file variables
- Elpy now supports project-specific RPC processes, see
  ``elpy-rpc-project-specific`` for how to use this
- ``M-*`` now works to go back where you came from after a ``M-.``
- Elpy now ships with a few dedicated snippets for YASnippet
- Support and require Jedi 0.6.0

New in Elpy 1.0
===============

- Version 0.9 was a release candidate, so this release focused on bug
  fixes instead of new features.
- ``elpy-enable`` now takes an optional argument that skips variable
  initialization for those users who prefer their own defaults for
  other modes.
- ``python-check.sh`` has been removed from Elpy, as the flake8 tool
  from pypi does everything it does, only better.
- Elpy will now start the helper subprocess in the root directory,
  avoiding accidental Python path clobbering.

New in Elpy 0.9
===============

- Elpy now officially support Python 2.6, 2.7 and 3.3 on Emacs 24.2
  and 24.3, with continuous integration tests thanks to
  `Travis CI`_.
- Extended support for Pydoc. ``C-u C-c C-d`` will now prompt for an
  auto-completed symbol to run Pydoc on. The pydoc output will be
  formatted and placed in a help buffer for easy review.
- Refactoring support is back. ``C-c C-r`` will pop up a refactoring
  wizard offering various refactoring options. Most of them depend on
  the presence of Rope, though, even if Jedi is used as a completion
  backend.
- The Rope backend has been extended to provide completions for
  modules in an import clause.
- New refactoring option: Add missing imports. This will search for
  undefined symbols in the current file and automatically add
  appropriate imports.
- ``C-c C-c (elpy-rgrep-symbol)`` now prompts for a regexp when a prefix
  argument is given instead of using the symbol at point.

.. _Travis CI: https://travis-ci.org/

New in Elpy 0.8
===============

Python Backend Rewrite
----------------------

- Elpy does not use Pymacs, Ropemacs and Ropemode anymore, but instead
  provides its own Python interface with the elpy package on PyPI.
- This not only should improve performance, but also enables using
  Jedi as an alternative backend for completion. Use ``M-x
  elpy-set-backend`` to change between rope and jedi. For now, this
  does disable all refactoring support, though.

Project Support
---------------

- Elpy now has built-in project support. The interface is rather
  simple: You can set ``elpy-project-root`` to the correct value in
  ``.dir-locals.el``, or just rely on the automatic detection. If you
  change your mind, you can always just ``elpy-set-project-root``.
- New dependency: Find File in Project (ffip), bound to ``C-c C-f`` by
  default. This will allow you to find files anywhere in your project
  using a search-as-you-type interface like ido.
- New dependency: nose, bound to ``C-c C-t`` by default. This will run
  the nosetests binary in the root of your current library directory.
  You can restrict the tests being run to the current test or the
  current module by adding prefix arguments.
- New function: Recursive grep for symbol, bound to ``C-c C-s`` by
  default. This will search for the symbol at point in the whole
  project.

New dependencies
----------------

- idomenu, bound to ``C-c C-j`` by default. This replaces the standard
  imenu interface with an ido-based search-as-you-type interface for
  definitions in the current buffer.
- virtualenv.el, replacing pyvirtualenv.el). Use ``M-x
  virtualenv-workon`` to enable a virtualenv.
- iedit.el, bound to ``M-,`` by default. This highlights all occurrences
  of the symbol at point or the active region in the current buffer or
  narrowing. When you edit any of them, all others will be edited the
  same. This allows some basic and very quick refactoring.
- New variable ``elpy-default-minor-modes`` which is run by ``elpy-mode``
  on startup. If you don’t want to use some modes, remove them from
  here.

Key Bindings and Functions
--------------------------

- The key bindings have been reworked and cleaned up. Sorry, this
  might cause confusion.
- Yasnippet is now on its own keybinding, ``C-c C-i``, instead of
  sharing the auto-complete interface. This was done because some
  snippets conflicted with legitimate, unsnippy completions.
- New function: Occur Definitions, bound to ``C-c C-o`` by default. This
  will run the standard occur command to show definitions (classes and
  functions) in your current buffer, giving you a very quick outline
  and the ability to jump to different definitions quickly.
- New function: Show Defun, bound to ``C-c C-q`` by default. This will
  show the current method and possibly class in the mode line, which
  is helpful in long functions.
- New functions: Forward/backward definition, bound to ``M-n`` and ``M-p``
  as well as ``<M-down>`` and ``<M-up>`` by default. These will jump to
  the next or previous definition (class or function), helping with
  quick navigation through a file.

Miscellaneous
-------------

- The documentation function (``C-c C-d``) now uses pydoc when a prefix
  arg is given.
- The web search function (``C-c C-w``) now searches for the current
  symbol by default. The tab-completing web documentation interface
  was removed and is scheduled to be replaced with a new pydoc
  interface in future versions.
- The ``python-check.sh`` is now shipped with elpy. If you load elpy.el
  before you load python.el, it should be the default
  ``python-check-command``.
