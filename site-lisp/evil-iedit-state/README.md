# evil-iedit-state
[![MELPA](http://melpa.org/packages/evil-iedit-state-badge.svg)](http://melpa.org/#/evil-iedit-state)
[![MELPA Stable](http://stable.melpa.org/packages/evil-iedit-state-badge.svg)](http://stable.melpa.org/#/evil-iedit-state)

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc/generate-toc again -->
**Table of Contents**

- [evil-iedit-state](#evil-iedit-state)
    - [Description](#description)
    - [Install](#install)
        - [Package manager](#package-manager)
        - [Manually](#manually)
    - [Key bindings](#key-bindings)
        - [State transitions](#state-transitions)
        - [In iedit state](#in-iedit-state)
        - [In iedit-insert state](#in-iedit-insert-state)

<!-- markdown-toc end -->

## Description

This package adds two new [Evil][evil-link] states:
- iedit state
- iedit-insert state

It has also a nice integration with [expand-region][] for quick edit
of the current selected text by pressing <kbd>e</kbd>.

## Install

### Package manager

You can either install `evil-iedit-state` from [MELPA][melpa-link]:

```
 M-x package-install evil-iedit-state
```

Or add it to your `Cask` file:

```elisp
(source melpa)

(depends-on "evil-iedit-state")
```

### Manually

Add `evil-iedit-state.el` to your load path. `evil-iedit-state` requires
both `iedit` and `evil` to be installed.

## Key bindings

### State transitions

    Key Binding    |       From         |          To
-------------------|:------------------:|:-------------------------:
<kbd>e</kbd>       | expand-region      | iedit
<kbd>ESC</kbd>     | iedit              | normal
<kbd>C-g</kbd>     | iedit              | normal
<kbd>ESC</kbd>     | iedit-insert       | iedit
<kbd>C-g</kbd>     | iedit-insert       | normal

To sum-up, in `iedit-insert state` you have to press <kbd>ESC</kbd> twice to
go back to the `normal state`. You can also at any time press <kbd>C-g</kbd>
to return to `normal state`.

**Note:** evil commands which switch to `insert state` will switch in
`iedit-insert state`.

### In iedit state

`iedit state` inherits from `normal state`, the following key bindings are
specific to `iedit state`.

    Key Binding   |                 Description
------------------|------------------------------------------------------------
<kbd>ESC</kbd>    | go back to `normal state`
<kbd>TAB</kbd>    | toggle current occurrence
<kbd>0</kbd>      | go to the beginning of the current occurrence
<kbd>$</kbd>      | go to the end of the current occurrence
<kbd>#</kbd>      | prefix all occurrences with an increasing number (<kbd>C-u</kbd> to choose the starting number).
<kbd>A</kbd>      | go to the end of the current occurrence and switch to `iedit-insert state`
<kbd>D</kbd>      | delete the occurrences
<kbd>F</kbd>      | restrict the scope to the function
<kbd>gg</kbd>     | go to first occurrence
<kbd>G</kbd>      | go to last occurrence
<kbd>I</kbd>      | go to the beginning of the current occurrence and switch to `iedit-insert state`
<kbd>J</kbd>      | increase the edition scope by one line below
<kbd>K</kbd>      | increase the edition scope by one line above
<kbd>L</kbd>      | restrict the scope to the current line
<kbd>n</kbd>      | go to next occurrence
<kbd>N</kbd>      | go to previous occurrence
<kbd>p</kbd>      | replace occurrences with last yanked (copied) text
<kbd>S</kbd>      | (substitute) delete the occurrences and switch to `iedit-insert state`
<kbd>V</kbd>      | toggle visibility of lines with no occurrence
<kbd>U</kbd>      | Up-case the occurrences
<kbd>C-U</kbd>    | down-case the occurrences

**Note:** <kbd>0</kbd>, <kbd>$</kbd>, <kbd>A</kbd> and <kbd>I</kbd> have the
default Vim behavior when used outside of an occurrence.

### In iedit-insert state

    Key Binding            |                 Description
---------------------------|------------------------------------------------------------
<kbd>ESC</kbd>             | go back to `iedit state`
<kbd>C-g</kbd>             | go back to `normal state`

[melpa-link]: http://melpa.org/
[evil-link]: https://gitorious.org/evil/pages/Home
[iedit]: https://github.com/tsdh/iedit
[expand-region]: https://github.com/magnars/expand-region.el
