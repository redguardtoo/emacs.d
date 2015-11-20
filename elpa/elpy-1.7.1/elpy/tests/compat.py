"""Python 2/3 compatibility definitions.

These are used by the rest of Elpy to keep compatibility definitions
in one place.

"""

import sys


if sys.version_info >= (3, 0):
    PYTHON3 = True
    import builtins
    from io import StringIO
else:
    PYTHON3 = False
    import __builtin__ as builtins  # noqa
    from StringIO import StringIO  # noqa
