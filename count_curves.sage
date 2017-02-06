def num_curves_with_conductor(N):
	DB=CremonaDatabase()
	Cs=DB.isogeny_classes(N)
	ans=0
	for j in range(len(Cs)):
		ans+=len(Cs[j])
	return ans

def num_curves_with_conductor_at_most(M):
	ans=0
	for N in range(1,M):
		ans+=num_curves_with_conductor(N)
		print ans
	return ans
