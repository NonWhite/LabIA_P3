from utils import *
import os
import re
import matplotlib.pyplot as plt
from copy import deepcopy as copy

def makePlot( data , xlabel , ylabel , filename ) :
	for i in range( len( data[ 'n' ] ) ) :
		plt.plot( data[ 'n' ][ i ] , data[ ylabel ][ i ] , 'b-' , linewidth = 2.0 )
	plt.xlabel( xlabel.capitalize() )
	plt.ylabel( ylabel.capitalize() )
	plt.savefig( filename )
	plt.clf()

def makePlots( directory , xlabel ) :
	files = [ directory + f for f in os.listdir( directory ) if f.endswith( '.out' ) ]
	lstStats = {}
	stats = { 'time' : [] , 'props' : [] , 'clauses' : [] , 'size' : [] }
	for name in files :
		currentn = int( name.split( '-' )[ 1 ] )
		if currentn not in lstStats :
			lstStats[ currentn ] = copy( stats )
		with open( name , 'r' ) as f :
			for line in f :
				if line.startswith( "SOLUTION" ) : break
				( key , value ) = line.split( " = " )
				lstStats[ currentn ][ key.lower() ].append( float( value ) )
	for key in stats :
		data = { 'n' : [] , key : [] }
		for n in lstStats :
			data[ 'n' ].append( [ n ] * len( lstStats[ n ][ key ] ) )
			data[ key ].append( lstStats[ n ][ key ] )
		makePlot( data , xlabel , key , "%s%s-%s.png" % ( directory , xlabel , key ) )
	return lstStats

def makePlots2( directory ) :
	files = [ directory + f for f in os.listdir( directory ) if f.endswith( '.out' ) ]
	stats = { 'time' : [] , 'props' : [] , 'clauses' : [] , 'size' : [] , 'satellites' : [] }
	for name in files :
		currentn = int( name.split( '-' )[ 1 ][ :2 ] )
		stats[ 'satellites' ].append( currentn )
		with open( name , 'r' ) as f :
			for line in f :
				if line.startswith( "SOLUTION" ) : break
				( key , value ) = line.split( " = " )
				stats[ key.lower() ].append( float( value ) )
	for key in stats :
		if key == 'satellites' : continue
		plt.xlabel( 'Satellites' )
		plt.ylabel( key.capitalize() )
		plt.plot( stats[ 'satellites' ] , stats[ key ] , 'b-' , linewidth = 2.0 )
		plt.savefig( "%s%s-%s.png" % ( directory , 'satellites' , key ) )
		plt.clf()

if __name__ == "__main__" :
	directory = '/Users/nonwhite/Dropbox/IME/Laboratorio IA/LabIA_P3/code/blocks/'
	makePlots( directory , 'blocks' )
	directory = '/Users/nonwhite/Dropbox/IME/Laboratorio IA/LabIA_P3/code/satellite/'
	makePlots2( directory )
