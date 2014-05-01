package optimize::methods;

use 5.006;
use strict;
use warnings FATAL => 'all';

use Exporter;
our @ISA = 'Exporter';
our @EXPORT = our @EXPORT_OK = qw(finalize_class);

=head1 NAME

optimize::methods - Hack to optimize foo->bar() into foo::bar('foo')

=head1 VERSION

Version 0.01

=cut

our $VERSION = '0.01';

require XSLoader;
XSLoader::load(__PACKAGE__);

sub import {
    if ( grep { $_ eq 'finalize_class' } @_ ) {
        my $import = $_[0]->can("SUPER::import");
        goto &$import;
    }
    
    my $self   = shift;
    my $caller = shift || caller;
    
    optimize_methods($caller);
    
    unshift @_, $self;
    goto &{$self->can("SUPER::import")};
}

sub unimport {
    my $self   = shift;
    my $caller = shift || caller;
    unfinalize_class($caller);
}

my %finalized;
sub finalize_class {
    my $class = shift;
    
    optimize_methods($class);

    if ( @_ && $_[0] =~ /\A[:-]?recursively\z/ ) {
        my $caller_isa = mro::get_linear_isa($class);
        shift @$caller_isa; # Remove this class
        
        for my $class ( @$caller_isa ) {
            finalize_class($class) unless $finalized{$class}++;
        }
    }
    
    my $stash = do { no strict; \%{"${class}::"} };
    for my $entry (keys %$stash) {
        next if $entry eq 'finalize_class';
        next if ref(\$stash->{$entry}) ne 'GLOB';
        my $cv = *{$stash->{$entry}}{CODE};
        next unless $cv;
        traverse_function($cv);
    }
    $finalized{$class}++;
}

optimize_methods(__PACKAGE__);

=head1 SYNOPSIS

After marking a class as finalized, B<some> method calls will be changed to
plain function calls.  This may provide some (likely minor) speed-ups, at
the cost of ignoring future changes to @ISA.

    package Foo {
        use optimize::methods; # Marks the class as final
        sub new { ... }
        sub method { ... }
        Foo->method(); # This becomes Foo::method('Foo')
    }

    my $obj           = Foo->new(); # This becomes Foo::new('Foo');
    my Foo $typed_obj = Foo->new(); # This becomes Foo::new('Foo');
    
    $obj->method();        # This is still a method call.
    $typed_obj->method();  # This becomes Foo::method($typed_obj), and woe
                           # is you if you put a non-Foo object in $typed_object

Basically, this module tries to convert method calls of the
BAREWORD->BAREWORD or $TYPED_OBJECT->BAREWORD style into direct calls
to the subroutines involved.

    package NormalClass {
        use optimize::methods;
        sub foo { NormalClass->bar() }
        sub bar { ... }
    }

In the example above, $self->bar() remains a method call, because
the compilation of the method call happens before bar() is defined.
It's possible to optimize that away by either predeclaring the
subroutine before the method that uses it (i.e. by having a C<sub bar;>),
or by calling the C<finalize_class> method on the current package:

    package NormalClass {
        use optimize::methods;
        sub foo { NormalClass->bar() }
        sub bar { ... }
        __PACKAGE__->finalize_class;
    }

C<finalize_class> will walk through all the subroutines of a given package,
trying to apply the optimization after the compilation phase.  This also
catches these cases:

    package NormalClass {
        use optimize::methods;
        sub foo {
            my NormalClass $self = shift;
            $self->bar(); # => NormalClass::bar($self)
        }
        sub bar { ... }
        __PACKAGE__->finalize_class;
    }


    package Bar {
        our @ISA = 'Foo';
        sub doof {
            shift->override_me();   # This remains a method call
        }
        sub override_me { say "Original" }
    }

    package Baz {
        use optimize::methods;
        our @ISA = 'Bar';
        sub override_me { say "Overriden" }
        __PACKAGE__->finalize_class(":recursively");
    }
    
    Baz->doof(); # Bar::doof('Baz'), outputs 'Overriden'
    Baz->method(); # Foo::method('Baz')

Finally, you can write C<use optimize::methods ":all"> to enable the optimization
B<everywhere>.  This means that you can get some speed gains from some modules
that were not written to account for this, like File::Spec or the pragmas,
but you open yourself to demons.

=head1 AUTHOR

Brian Fraser, C<< <brian.fraser at booking.com> >>

=head1 BUGS

Please report any bugs or feature requests to C<bug-optimize-methods at rt.cpan.org>, or through
the web interface at L<http://rt.cpan.org/NoAuth/ReportBug.html?Queue=optimize-methods>.  I will be notified, and then you'll
automatically be notified of progress on your bug as I make changes.




=head1 SUPPORT

You can find documentation for this module with the perldoc command.

    perldoc optimize::methods


You can also look for information at:

=over 4

=item * RT: CPAN's request tracker (report bugs here)

L<http://rt.cpan.org/NoAuth/Bugs.html?Dist=optimize-methods>

=item * AnnoCPAN: Annotated CPAN documentation

L<http://annocpan.org/dist/optimize-methods>

=item * CPAN Ratings

L<http://cpanratings.perl.org/d/optimize-methods>

=item * Search CPAN

L<http://search.cpan.org/dist/optimize-methods/>

=back


=head1 ACKNOWLEDGEMENTS


=head1 LICENSE AND COPYRIGHT

Copyright 2014 Brian Fraser.

This program is free software; you can redistribute it and/or modify it
under the terms of the the Artistic License (2.0). You may obtain a
copy of the full license at:

L<http://www.perlfoundation.org/artistic_license_2_0>

Any use, modification, and distribution of the Standard or Modified
Versions is governed by this Artistic License. By using, modifying or
distributing the Package, you accept this license. Do not use, modify,
or distribute the Package, if you do not accept this license.

If your Modified Version has been derived from a Modified Version made
by someone other than you, you are nevertheless required to ensure that
your Modified Version complies with the requirements of this license.

This license does not grant you the right to use any trademark, service
mark, tradename, or logo of the Copyright Holder.

This license includes the non-exclusive, worldwide, free-of-charge
patent license to make, have made, use, offer to sell, sell, import and
otherwise transfer the Package with respect to any patent claims
licensable by the Copyright Holder that are necessarily infringed by the
Package. If you institute patent litigation (including a cross-claim or
counterclaim) against any party alleging that the Package constitutes
direct or contributory patent infringement, then this Artistic License
to you shall terminate on the date that such litigation is filed.

Disclaimer of Warranty: THE PACKAGE IS PROVIDED BY THE COPYRIGHT HOLDER
AND CONTRIBUTORS "AS IS' AND WITHOUT ANY EXPRESS OR IMPLIED WARRANTIES.
THE IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
PURPOSE, OR NON-INFRINGEMENT ARE DISCLAIMED TO THE EXTENT PERMITTED BY
YOUR LOCAL LAW. UNLESS REQUIRED BY LAW, NO COPYRIGHT HOLDER OR
CONTRIBUTOR WILL BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, OR
CONSEQUENTIAL DAMAGES ARISING IN ANY WAY OUT OF THE USE OF THE PACKAGE,
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


=cut

1; # End of optimize::methods
