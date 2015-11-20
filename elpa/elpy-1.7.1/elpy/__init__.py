# Elpy, the Emacs Lisp Python Environment

# Copyright (C) 2013 Jorgen Schaefer

# Author: Jorgen Schaefer <contact@jorgenschaefer.de>
# URL: http://github.com/jorgenschaefer/elpy

# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; either version 3
# of the License, or (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.

"""The Emacs Lisp Python Environment.

Elpy is a mode for Emacs to support writing Python code. This package
provides the backend within Python to support auto-completion,
documentation extraction, and navigation.

Emacs will start the protocol by running the module itself, like so:

  python -m elpy

This will emit a greeting string on a single line, and then wait for
the protocol to start. Details of the protocol can be found in
elpy.rpc.

This package is unlikely to be useful on its own.

"""

__author__ = "Jorgen Schaefer"
__version__ = "1.7.1"
__license__ = "GPL"
