.. SPDX-License-Identifier: BSD-3-Clause
.. SPDX-FileCopyrightText: Copyright TF-RMM Contributors.

Coding Standard
===============

This document describes the coding rules to follow to contribute to the project.

General
-------

The following coding standard is derived from `MISRA C:2012 Guidelines`_,
`TF-A coding style`_ and `Linux kernel coding style`_ coding standards.

File Encoding
-------------

The source code must use the **UTF-8** character encoding. Comments and
documentation may use non-ASCII characters when required (e.g. Greek letters
used for units) but code itself is still limited to ASCII characters.

Language
--------

The primary language for comments and naming must be International English. In
cases where there is a conflict between the American English and British English
spellings of a word, the American English spelling is used.

Exceptions are made when referring directly to something that does not use
international style, such as the name of a company. In these cases the existing
name should be used as-is.

C Language Standard
-------------------

The C language mode used for |RMM| is *GNU11*. This is the "GNU dialect of ISO
C11", which implies the *ISO C11* standard with GNU extensions.

Both GCC and Clang compilers have support for *GNU11* mode, though
Clang does lack support for a small number of GNU extensions. These
missing extensions are rarely used, however, and should not pose a problem.

Length
------

- Each file, function and scopes should have a logical uniting theme.

  No length limit is set for a file.

- A function should be 24 lines maximum.

  This will not be enforced, any function being longer should trigger a
  discussion during the review process.

- The recommended maximum line length is 80 characters, except for string literals
  as it would make any search for it more difficult. A maximum length of 100
  characters is enforced by the coding guidelines static check.

- A variable should not be longer than 31 characters.

  Although the `C11 specification`_ specifies that the number of signitificant
  characters in an identifier is implementation defined it sets the translation
  limit to the 31 initial characters.

+--------------+-----------------------------------+
|   TYPE       |             LIMIT                 |
+==============+===================================+
|   function   |     24 lines (not enforced)       |
+--------------+-----------------------------------+
|     line     |          100 characters           |
+--------------+-----------------------------------+
|  identifier  |          31 characters            |
+--------------+-----------------------------------+


Headers/Footers
---------------

- Include guards:

.. code:: c

   #ifndef FILE_NAME_H
   #define FILE_NAME_H

   <header content>

   #endif /* FILE_NAME_H */

- Include statement variant is <>:

.. code:: c

   #include <file.h>


- Include files should be alphabetically ordered:

.. code:: c

   #include <axxxx.h>
   #include <bxxxx.h>
   [...]
   #include <zxxxx.h>

- If possible, use forward declaration of struct types in public headers.
  This will reduce interdependence of header file inclusion.

.. code:: c

   #include <axxxx.h>
   #include <bxxxx.h>
   [...]
   /* forward declaration */
   struct x;
   void foo(struct *x);


Naming conventions
------------------

- Case:
  Functions and variables must be in Snake Case

.. code:: c

  unsigned int my_snake_case_variable = 0U;

  void my_snake_case_function(void)
  {
	  [...]
  }


- Local variables should be declared at the top of the closest opening scope
  and should be short.

  We won't enforce a length, and defining short is difficult, this motto
  (from Linux) catches the spirit

    +---------------------------------------------------------------------------+
    | LOCAL variable names should be short, and to the point.                   |
    |                                                                           |
    | If you have some random integer loop counter,                             |
    | it should probably be called i.                                           |
    |                                                                           |
    | Calling it loop_counter is non-productive,                                |
    | if there is no chance of it being mis-understood.                         |
    |                                                                           |
    | Similarly, tmp can be just about any type of variable that is             |
    | used to hold a temporary value.                                           |
    |                                                                           |
    | If you are afraid to mix up your local variable names,                    |
    | you have another problem.                                                 |
    +---------------------------------------------------------------------------+

.. code:: c

  int foo(const int a)
  {
	  int c; /* needed in the function */
	  c = a; /* MISRA-C rules recommend to not modify arguments variables */

	  if (c == 42) {
	          int b; /* needed only in this "if" statment */

		  b = bar(); /* bar will return an int */
		  if (b != -1) {
		          c += b;
		  }
	  }
	  return c;
  }

- Use an appropraite prefix for public API of a component. For example,
  if the component name is `bar`, then the init API of the component
  should be called `bar_init()`.

Indentation
-----------

Use **tabs** for indentation. The use of spaces for indentation is forbidden
except in the case where a term is being indented to a boundary that cannot be
achieved using tabs alone.

Tab spacing should be set to **8 characters**.

Trailing whitespaces or tabulations are not allowed and must be trimmed.

Spacing
-------

Single spacing should be used around most operators, including:

- Arithmetic operators (``+``, ``-``, ``/``, ``*``, ``%``)
- Assignment operators (``=``, ``+=``, etc)
- Boolean operators (``&&``, ``||``)
- Comparison operators (``<``, ``>``, ``==``, etc)
- Shift operators (``>>``, ``<<``)
- Logical operators (``&``, ``|``, etc)
- Flow control (``if``, ``else``, ``switch``, ``while``, ``return``, etc)

No spacing should be used around the following operators

- Cast (``()``)
- Indirection (``*``)

Braces
------

- Use K&R style for statements.

- Function opening braces are on a new line.

- Use braces even for singled line.


.. code:: c

  void function(void)
  {
	  /* if statement */
	  if (my_test) {
		  do_this();
		  do_that();
	  }

	  /* if/else statement */
	  if (my_Test) {
		  do_this();
		  do_that();
	  } else {
		  do_other_this();
	  }
  }

Commenting
----------

Double-slash style of comments (//) is not allowed, below are examples of
correct commenting.

.. code:: c

  /*
   * This example illustrates the first allowed style for multi-line comments.
   *
   * Blank lines within multi-lines are allowed when they add clarity or when
   * they separate multiple contexts.
   */

.. code:: c

  /**************************************************************************
   * This is the second allowed style for multi-line comments.
   *
   * In this style, the first and last lines use asterisks that run the full
   * width of the comment at its widest point.
   *
   * This style can be used for additional emphasis.
   *************************************************************************/

.. code:: c

  /* Single line comments can use this format */

.. code:: c

  /***************************************************************************
   * This alternative single-line comment style can also be used for emphasis.
   **************************************************************************/


Error return values and Exception handling
------------------------------------------

- Function return type must be explicitly defined.

- Unless specifed otherwise by an official specification, return values must be
  used to return success or failure (Standard Posix error codes).

  Return an integer if the function is an action or imperative command
      Failure: -Exxx (STD posix error codes, unless specified otherwise)

      Success: 0

  Return a boolean if the function is as predicate
      Failure: false

      Success: true

- If a function returns error information, then that error information shall
  be tested.

  Exceptions are allowed for STDLIB functions (memcpy/printf/...) in which case
  it must be void casted.

.. code:: c

  #define MY_TRANSFORMED_ERROR  (-1)

  void my_print_function(struct my_struct in_mystruct)
  {
	  long long transformed_a = my_transform_a(in_mystruct.a);

	  if (transform_a != MY_TRANSFORMED_ERROR) {
		  (void)printf("STRUCT\n\tfield(a): %ll\n", transformed_a);
	  } else {
		  (void)printf("STRUCT\n\tERROR %ll\n", transformed_a);
	  }
  }


Use of asserts and panic
------------------------

Assertions, as a general rule, are only used to catch errors during
development cycles and are removed from production binaries. They are
useful to document pre-conditions for a function or impossible conditions
in code. They are not substitutes for proper error checking and any
expression used to test an assertion must not have a side-effect.

For example,

.. code:: c

  assert(--i == 0);

should not be used in code.

Assertions can be used to validate input arguments to an API as long as
the caller and callee are within the same trust boundary.

``panic()`` is used in places wherein it is not possible to continue the
execution of program sensibly. It should be used sparingly within code
and, if possible, instead of panic(), components should return error
back to the caller and the caller can decide on the appropriate action.
This is particularly useful to build resilence to the program wherein
non-functional part of the program can be disabled and, if possible,
other functional aspects of the program can be kept running.

Using COMPILER_ASSERT to check for compile time data errors
-----------------------------------------------------------

Where possible, use the ``COMPILER_ASSERT`` macro to check the validity of
data known at compile time instead of checking validity at runtime, to avoid
unnecessary runtime code.

For example, this can be used to check that the assembler's and compiler's views
of the size of an array is the same.

.. code:: c

  #include <utils_def.h>

  define MY_STRUCT_SIZE 8 /* Used by assembler source files */

  struct my_struct {
      uint32_t arg1;
      uint32_t arg2;
  };

  COMPILER_ASSERT(MY_STRUCT_SIZE == sizeof(struct my_struct));


If ``MY_STRUCT_SIZE`` in the above example were wrong then the compiler would
emit an error like this:

::

  my_struct.h:10:1: note: in expansion of macro 'COMPILER_ASSERT'
   10 | COMPILER_ASSERT(MY_STRUCT_SIZE == sizeof(struct my_struct));
      | ^~~~~~~~~~~~~~~

.. note::

    For CBMC analysis some of the compile assertions are not valid (for example
    due to the missing padding from certain structures, or due to smaller
    ``GRANULE_SIZE``). In this case the macro ``COMPILER_ASSERT_NO_CBMC`` should
    be used which behaves as ``COMPILER_ASSERT`` for regular builds, and always
    passes for CBMC build.

Data types, structures and typedefs
-----------------------------------

- Data Types:

The |RMM| codebase should be kept as portable as possible for 64-bits platforms.
To help with this, the following data type usage guidelines should be followed:

- Where possible, use the built-in *C* data types for variable storage (for
  example, ``char``, ``int``, ``long long``, etc) instead of the standard *C11*
  types. Most code is typically only concerned with the minimum size of the
  data stored, which the built-in *C* types guarantee.

- Avoid using the exact-size standard *C11* types in general (for example,
  ``uint16_t``, ``uint32_t``, ``uint64_t``, etc) since they can prevent the
  compiler from making optimizations. There are legitimate uses for them,
  for example to represent data of a known structure. When using them in a
  structure definition, consider how padding in the structure will work across
  architectures.

- Use ``int`` as the default integer type - it's likely to be the fastest on all
  systems. Also this can be assumed to be 32-bit as a consequence of the
  `Procedure Call Standard for the Arm 64-bit Architecture`_ .

- Avoid use of ``short`` as this may end up being slower than ``int`` in some
  systems. If a variable must be exactly 16-bit, use ``int16_t`` or
  ``uint16_t``.

- ``long`` are defined as LP64 (64-bit), this is guaranteed to be 64-bit.

- Use ``char`` for storing text. Use ``uint8_t`` for storing other 8-bit data.

- Use ``unsigned`` for integers that can never be negative (counts,
  indices, sizes, etc). |RMM| intends to comply with MISRA "essential type"
  coding rules (10.X), where signed and unsigned types are considered different
  essential types. Choosing the correct type will aid this. MISRA static
  analysers will pick up any implicit signed/unsigned conversions that may lead
  to unexpected behaviour.

- For pointer types:

  - If an argument in a function declaration is pointing to a known type then
    simply use a pointer to that type (for example: ``struct my_struct *``).

  - If a variable (including an argument in a function declaration) is pointing
    to a general, memory-mapped address, an array of pointers or another
    structure that is likely to require pointer arithmetic then use
    ``uintptr_t``. This will reduce the amount of casting required in the code.
    Avoid using ``unsigned long`` or ``unsigned long long`` for this purpose;
    it may work but is less portable.

  - Use of ``void *`` is generally discouraged. Although it is useful to
    represent pointers to types that are abstracted away from the callers and
    has useful implicit cast properties, for the sake of a more uniform code
    base, we encourage use of ``uintptr_t`` where possible.

  - Avoid pointer arithmetic generally (as this violates MISRA C 2012 rule
    18.4) and especially on void pointers (as this is only supported via
    language extensions and is considered non-standard). In |RMM|, setting the
    ``W`` build flag to ``W=3`` enables the *-Wpointer-arith* compiler flag and
    this will emit warnings where pointer arithmetic is used.

  - Use ``ptrdiff_t`` to compare the difference between 2 pointers.

- Use ``size_t`` when storing the ``sizeof()`` something.

- Use ``ssize_t`` when returning the ``sizeof()`` something from a function
  that can also return an error code; the signed type allows for a negative
  return code in case of error. This practice should be used sparingly.

- Use ``uint64_t`` to store the contents of an AArch64 register or
  represent a 64-bit value. Use of ``unsigned long`` or ``u_register_t``
  for these purposes is discouraged.

These guidelines should be updated if additional types are needed.

- Typedefs:

Typedef should be avoided and used only to create opaque types.
An opaque data type is one whose concrete data structure is not publicly
defined. Opaque data types can be used on handles to resources that the caller
is not expected to address directly.

.. code:: c

	  /* File main.c */
	  #include <my_lib.h>

	  int main(void)
	  {
		context_t	*context;
		int		res;

		context = my_lib_init();

		res = my_lib_compute(context, "2x2");
		if (res == -EMYLIB_ERROR) {
			return -1
		}

		return res;
	  }

.. code:: c

	  /* File my_lib.h */
	  #ifndef MY_LIB_H
	  #define MY_LIB_H

	  typedef struct my_lib_context {
	    [...] /* whatever internal private variables you need in my_lib */
	  } context_t;

	  #endif /* MY_LIB_H */

Macros and Enums
----------------

- Favor functions over macros.

- Preprocessor macros and enums values are written in all uppercase text.

- A numerical value shall be typed.

.. code:: c

	/* Common C usage​ */
	#define MY_MACRO 4UL

	/* If used in C and ASM (included from a .S file)​ */
	#define MY_MACRO UL(4)

- Expressions resulting from the expansion of macro parameters must be enclosed
  in parentheses.

- A macro parameter immediately following a # operator mustn't be immediately
  followed by a ## operator.

.. code:: c

   #define SINGLE_HASH_OP(x)		(#x)		/* allowed */
   #define SINGLE_DOUBLE_HASH_OP(x, y)	(x ## y)	/* allowed */
   #define MIXED_HASH_OP(x, y)		(#x ## y)	/* not allowed */

- Avoid defining macros that affect the control flow (i.e. avoid using
  return/goto in a macro).

- Macro with multiple statements can be enclosed in a do-while block or in a
  expression statement.

.. code:: c

	  int foo(char **b);

	  #define M1(a, b)			\
		  do {				\
			if ((a) == 5) {		\
				foo((b));	\
			}			\
		  } while (false)

	  #define M2(a, b)		\
		  ({			\
		  if ((a) == 5) {	\
			  foo((b));	\
		  }			\
		  })

	  int foo(char **b)
	  {
		  return 42;
	  }

	  int main(int ac, char **av)
	  {
		  if (ac == 1) {
			  M1(ac, av);
		  } else if (ac == 2) {
			  M2(ac, av);
		  } else {
			  return -1;
		  }

		  return ac;
	  }

Switch statements
-----------------

- Return in a *case* are allowed.

- Fallthrough are allowed as long as they are commented.

- Do not rely on type promotion between the switch type and the case type.

Inline assembly
---------------

- Favor C language over assembly language.

- Document all usage of assembly.

- Do not mix C and ASM in the same file.

Libc functions that are banned or to be used with caution
---------------------------------------------------------

Below is a list of functions that present security risks.

+------------------------+--------------------------------------+
|    libc function       | Comments                             |
+========================+======================================+
| ``strcpy, wcscpy``,    | use strlcpy instead                  |
| ``strncpy``            |                                      |
+------------------------+--------------------------------------+
| ``strcat, wcscat``,    | use strlcat instead                  |
| ``strncat``            |                                      |
+------------------------+--------------------------------------+
| ``sprintf, vsprintf``  | use snprintf, vsnprintf              |
|                        | instead                              |
+------------------------+--------------------------------------+
| ``snprintf``           | if used, ensure result fits in buffer|
|                        | i.e : snprintf(buf,size...) < size   |
+------------------------+--------------------------------------+
| ``vsnprintf``          | if used, inspect va_list match types |
|                        | specified in format string           |
+------------------------+--------------------------------------+
| ``strtok, strtok_r``,  | Should not be used                   |
| ``strsep``             |                                      |
+------------------------+--------------------------------------+
| ``ato*``               | Should not be used                   |
+------------------------+--------------------------------------+
| ``*toa``               | Should not be used                   |
+------------------------+--------------------------------------+

The use of above functions are discouraged and will only be allowed
in justified cases after a discussion has been held either on the mailing
list or during patch review and it is agreed that no alternative to their
use is available. The code containing the banned APIs must properly justify
their usage in the comments.

The above restriction does not apply to Third Party IP code inside the ``ext/``
directory.

-----------

.. _`Procedure Call Standard for the Arm 64-bit Architecture`: https://developer.arm.com/docs/ihi0055/latest/
.. _`Linux kernel coding style`: https://www.kernel.org/doc/html/latest/process/coding-style.html
.. _`MISRA C:2012 Guidelines`: https://www.misra.org.uk/Activities/MISRAC/tabid/160/Default.aspx
.. _`TF-A coding style`: https://trustedfirmware-a.readthedocs.io/en/latest/process/coding-style.html
.. _`C11 specification`: https://en.wikipedia.org/wiki/C11_(C_standard_revision)
