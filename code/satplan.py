import sys
import os
from utils import *
from solver import Solver

DEBUG = False

class SatPlan( Solver ) :
	def preprocess( self ) :
		print "#PREDICATES = %s" % len( self.predicates )
		print "#ACTIONS = %s" % len( self.actions )
		print "#IMPLICATIONS = %s" % len( self.implications )
	
	def getID( self , prop ) :
		if prop == None : return ''
		time = prop[ 'time' ]
		pos = 0
		if prop[ 'isaction' ] :
			pos = getAllValues( self.actions , 'name' ).index( prop[ 'name' ] )
			pos += self.idactions
		else :
			pos = self.predicates.index( prop[ 'name' ] )
			pos += self.idpredicates
		ID = pos + time * self.total
		if not prop[ 'state' ] : ID = -ID
		return ID
	
	def getProposition( self , ID ) :
		isnegation = False
		if ID < 0 :
			isnegation = True
			ID = -ID
		pos = ( ID % self.total ) - 1
		resp = ''
		if pos >= len( self.predicates ) :
			pos -= len( self.predicates )
			resp = self.actions[ pos ][ 'name' ]
		else :
			resp = self.predicates[ pos ]
		resp = ( "~" if isnegation else "" ) + resp
		return resp

	# Convert propositions in CNF File
	def generateCNF( self ) :
		filename = "%s/%s_%s.cnf" % ( self.directory , self.domain[ 'domain_name' ] , self.steps )
		numvars = len( self.predicates ) + self.total * self.steps
		numclauses = len( self.implications ) + len( self.start ) + len( self.goal )
		f = open( filename , 'w' )
		print "Generating %s" % filename
		f.write( "p cnf %s %s\n" % ( numvars , numclauses ) )
		# Add start propositions
		for prop in self.start :
			if 'time' not in prop : prop[ 'time' ] = 0
			if 'isaction' not in prop : prop[ 'isaction' ] = False
			if DEBUG : f.write( "%s%s(0)\n" % ( "NOT " if not prop[ 'state' ] else "" , prop[ 'name' ] ) )
			f.write( "%s 0\n" % self.getID( prop ) )
		# Add all axioms
		for imp in self.implications :
			left = imp[ 'left' ]
			right = imp[ 'right' ]
			factor = ( 1 if right == None else -1 )
			for ifc in left :
				if DEBUG : f.write( "%s%s(%s) %s" % ( "NOT " if not ifc[ 'state' ] else "" , ifc[ 'name' ] , ifc[ 'time' ] , "AND " if len( left ) > 1 else "" ) )
				f.write( "%s " % ( factor * self.getID( ifc ) ) )
			if DEBUG :
				if right != None : f.write( " => %s%s(%s)\n" % ( "NOT " if not right[ 'state' ] else "" , right[ 'name' ] , right[ 'time' ] ) )
				else : f.write( "\n" )
			f.write( "%s 0\n" % self.getID( right ) )
		# Add goal propositions
		for prop in self.goal :
			prop[ 'time' ] = self.steps
			prop[ 'isaction' ] = False
			if DEBUG : f.write( "%s%s(%s)\n" % ( "NOT " if not prop[ 'state' ] else "" , prop[ 'name' ] , self.steps ) )
			f.write( "%s 0\n" % self.getID( prop ) )

		return filename
	
	def addAction( self ) :
		# Add axioms of preconditions
		for act in self.actions :
			left = [ formProposition( act[ 'name' ] , True , self.steps , True ) ]
			for pre in act[ 'precondition' ] :
				right = formProposition( pre[ 'name' ] , pre[ 'state' ] , self.steps , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of effect
		for act in self.actions :
			left = [ formProposition( act[ 'name' ] , True , self.steps , True ) ]
			for pre in act[ 'effect' ] :
				right = formProposition( pre[ 'name' ] , pre[ 'state' ] , self.steps + 1 , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of persistence
		for act in self.actions :
			for pers in act[ 'persistence' ] :
				left = [ formProposition( act[ 'name' ] , True , self.steps , True ) , \
							formProposition( pers[ 'name' ] , True , self.steps , False ) ]
				right = formProposition( pers[ 'name' ] , True , self.steps + 1 , False )
				self.implications.append( { 'left' : left , 'right' : right } )
				left = [ formProposition( act[ 'name' ] , True , self.steps , True ) , \
							formProposition( pers[ 'name' ] , False , self.steps , False ) ]
				right = formProposition( pers[ 'name' ] , False , self.steps + 1 , False )
				self.implications.append( { 'left' : left , 'right' : right } )
		# Add axioms of continuity
		left = []
		for act in self.actions :
			left.append( formProposition( act[ 'name' ] , True , self.steps , True ) )
		self.implications.append( { 'left' : left , 'right' : None } )
		# Add axioms of not paralelism
		for i in range( len( self.actions ) ) :
			left = [ formProposition( self.actions[ i ][ 'name' ] , True , self.steps , True ) ]
			for j in range( len( self.actions ) ) :
				if i == j : continue
				right = formProposition( self.actions[ j ][ 'name' ] , False , self.steps , True )
				self.implications.append( { 'left' : left , 'right' : right } )

		self.steps += 1
		print "#IMPLICATIONS = %s" % len( self.implications )
	
	def parseSolution( self , cnfsolution ) :
		sol = [ self.getProposition( int( w ) ) for w in cnfsolution ]
		idx = 0
		resp = []
		for k in range( self.steps + 1 ) :
			count = 0
			t = {}
			while idx < len( sol ) and count < self.total :
				if sol[ idx ].find( '~' ) < 0 :
					if sol[ idx ] in getAllValues( self.actions , 'name' ) :
						t[ 'action' ] = sol[ idx ]
					else :
						if 'props' not in t : t[ 'props' ] = []
						t[ 'props' ].append( sol[ idx ] )
				idx += 1
				count += 1
			resp.append( t )
		return resp

if __name__ == "__main__" :
	if len( sys.argv ) >= 3 :
		if len( sys.argv ) > 3 : DEBUG = sys.argv[ 3 ]
		stripsfile = sys.argv[ 1 ]
		solver = SatPlan( stripsfile )
		situationfile = sys.argv[ 2 ]
		solver.solve( situationfile )
	else :
		print 'Usage: %s [strips_filename] [scenary_filename]' % sys.argv[ 0 ]
